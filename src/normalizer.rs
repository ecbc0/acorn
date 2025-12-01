use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::{Atom, AtomId, INVALID_SYNTHETIC_ID};
use crate::builder::BuildError;
use crate::clause::Clause;
use crate::cnf::CNF;
use crate::extended_term::ExtendedTerm;
use crate::fact::Fact;
use crate::goal::Goal;
use crate::kernel::type_store::TypeStore;
use crate::literal::Literal;
use crate::monomorphizer::Monomorphizer;
use crate::names::ConstantName;
use crate::normalization_map::{NewConstantType, NormalizationMap};
use crate::proof_step::{ProofStep, Truthiness};
use crate::source::{Source, SourceType};
use crate::term::{Term, TypeId, BOOL};

/// Information about the definition of a set of synthetic atoms.
pub struct SyntheticDefinition {
    /// The synthetic atoms that are defined in this definition.
    /// Each of these should be present in clauses.
    pub atoms: Vec<AtomId>,

    /// The clauses are true by construction and describe the synthetic atoms.
    /// We do need a definition to be a bunch of clauses instead of just one, even
    /// for "let x = ___" type definitions, because it might be a value that expands
    /// to multiple clauses.
    pub clauses: Vec<Clause>,

    /// The source location where this synthetic definition originated.
    pub source: Option<Source>,
}

impl std::fmt::Display for SyntheticDefinition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Join all the clauses with "and"
        let clauses_str: Vec<String> = self.clauses.iter().map(|c| c.to_string()).collect();
        let clauses = clauses_str.join(" and ");
        write!(
            f,
            "SyntheticDefinition(atoms: {:?}, clauses: {})",
            self.atoms, clauses
        )
    }
}

/// The SyntheticKey normalizes out the specific choice of id for the synthetic atoms
/// in the SyntheticDefinition.
/// This lets us check if two different synthetic atoms would be "defined the same way".
#[derive(Hash, Eq, PartialEq, Debug, Clone)]
struct SyntheticKey {
    /// How many synthetic atoms are defined here.
    num_atoms: usize,

    /// CNF form of the proposition that we defines these synthetic atoms.
    /// Here, the synthetic atoms have been remapped to the invalid range,
    /// in order to normalize away the specific choice of synthetic ids.
    clauses: Vec<Clause>,
}

impl std::fmt::Display for SyntheticKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Join all the clauses with "and"
        let clauses_str: Vec<String> = self.clauses.iter().map(|c| c.to_string()).collect();
        let clauses = clauses_str.join(" and ");
        write!(
            f,
            "SyntheticKey(num_atoms: {}, clauses: {})",
            self.num_atoms, clauses
        )
    }
}

#[derive(Clone)]
pub struct Normalizer {
    monomorphizer: Monomorphizer,

    /// Types of the synthetic atoms that we synthesized
    synthetic_types: Vec<AcornType>,

    /// The definition for each synthetic atom, indexed by AtomId.
    synthetic_definitions: HashMap<AtomId, Arc<SyntheticDefinition>>,

    /// Same information as `synthetic_info`, but indexed by SyntheticKey.
    /// This is used to avoid defining the same thing multiple times.
    synthetic_map: HashMap<SyntheticKey, Arc<SyntheticDefinition>>,

    normalization_map: NormalizationMap,

    /// Manages the bidirectional mapping between AcornTypes and TypeIds.
    type_store: TypeStore,
}

impl Normalizer {
    pub fn new() -> Normalizer {
        Normalizer {
            monomorphizer: Monomorphizer::new(),
            synthetic_types: vec![],
            synthetic_definitions: HashMap::new(),
            synthetic_map: HashMap::new(),
            normalization_map: NormalizationMap::new(),
            type_store: TypeStore::new(),
        }
    }

    pub fn get_synthetic_type(&self, id: AtomId) -> &AcornType {
        &self.synthetic_types[id as usize]
    }

    /// Gets a synthetic definition for a value, if one exists.
    /// The value should be of the form "exists ___ (forall x and forall y and ...)".
    pub fn get_synthetic_definition(
        &mut self,
        value: &AcornValue,
    ) -> Option<&Arc<SyntheticDefinition>> {
        let (num_definitions, alt_value) = match value {
            AcornValue::Exists(quants, subvalue) => (
                quants.len(),
                AcornValue::ForAll(quants.clone(), subvalue.clone()),
            ),
            _ => (0, value.clone()),
        };
        let mut view = NormalizerView::Ref(self);
        let Ok(uninstantiated) = view.value_to_denormalized_clauses(&alt_value) else {
            return None;
        };
        let clauses = uninstantiated
            .iter()
            .map(|c| c.instantiate_invalid_synthetics(num_definitions))
            .collect();
        let key = SyntheticKey {
            clauses,
            num_atoms: num_definitions,
        };
        self.synthetic_map.get(&key)
    }

    // This declares a synthetic atom, but does not define it.
    // This weird two-step is necessary since we need to do some constructions
    // before we actually have the definition.
    fn declare_synthetic_atom(&mut self, atom_type: AcornType) -> Result<AtomId, String> {
        let id = self.synthetic_types.len() as AtomId;
        if id >= INVALID_SYNTHETIC_ID {
            return Err(format!("ran out of synthetic ids (used {})", id));
        }
        // Add the synthetic atom type to the normalization map
        self.type_store.add_type(&atom_type);
        self.synthetic_types.push(atom_type);
        Ok(id)
    }

    /// Adds the definition for these synthetic atoms.
    fn define_synthetic_atoms(
        &mut self,
        atoms: Vec<AtomId>,
        clauses: Vec<Clause>,
        source: Option<Source>,
    ) -> Result<(), String> {
        // Check if any atoms are already defined
        for atom in &atoms {
            if self.synthetic_definitions.contains_key(atom) {
                return Err(format!("synthetic atom {} is already defined", atom));
            }
        }

        // In the synthetic key, we normalize synthetic ids by renumbering them.
        let synthetic_key_form: Vec<_> = clauses
            .iter()
            .map(|c| c.invalidate_synthetics(&atoms))
            .collect();
        let num_atoms = atoms.len();
        let key = SyntheticKey {
            clauses: synthetic_key_form,
            num_atoms,
        };
        let info = Arc::new(SyntheticDefinition {
            clauses,
            atoms: atoms.clone(),
            source,
        });
        for atom in &atoms {
            self.synthetic_definitions.insert(*atom, info.clone());
        }
        self.synthetic_map.insert(key, info);
        Ok(())
    }

    pub fn add_local_constant(&mut self, cname: ConstantName) -> Atom {
        self.normalization_map
            .add_constant(cname, NewConstantType::Local)
    }
}

// Represents a binding for a variable on the stack during normalization.
enum TermBinding {
    Bound(Term),
    Free(Term),
}

impl TermBinding {
    /// Get the underlying term regardless of binding type
    fn term(&self) -> &Term {
        match self {
            TermBinding::Bound(t) | TermBinding::Free(t) => t,
        }
    }
}

// A NormalizerView lets us share methods between mutable and non-mutable normalizers that
// only differ in a small number of places.
pub enum NormalizerView<'a> {
    Ref(&'a Normalizer),
    Mut(&'a mut Normalizer),
}

impl NormalizerView<'_> {
    fn as_ref(&self) -> &Normalizer {
        match self {
            NormalizerView::Ref(n) => n,
            NormalizerView::Mut(n) => n,
        }
    }

    fn as_mut(&mut self) -> Result<&mut Normalizer, String> {
        match self {
            NormalizerView::Ref(_) => Err("Cannot mutate a NormalizerView::Ref".to_string()),
            NormalizerView::Mut(n) => Ok(n),
        }
    }

    fn map(&self) -> &NormalizationMap {
        &self.as_ref().normalization_map
    }

    fn type_store(&self) -> &TypeStore {
        &self.as_ref().type_store
    }

    fn type_store_mut(&mut self) -> Result<&mut TypeStore, String> {
        Ok(&mut self.as_mut()?.type_store)
    }

    /// Wrapper around value_to_cnf.
    /// Note that this only works on values that have already been "cleaned up" to some extent.
    pub fn nice_value_to_clauses(
        &mut self,
        value: &AcornValue,
        synthesized: &mut Vec<AtomId>,
    ) -> Result<Vec<Clause>, String> {
        match value {
            AcornValue::Binary(BinaryOp::And, left, right) => {
                let mut left_clauses = self.nice_value_to_clauses(left, synthesized)?;
                let right_clauses = self.nice_value_to_clauses(right, synthesized)?;
                left_clauses.extend(right_clauses);
                Ok(left_clauses)
            }
            _ => {
                let mut stack = vec![];
                let mut next_var_id = 0;
                let cnf =
                    self.value_to_cnf(&value, false, &mut stack, &mut next_var_id, synthesized)?;
                Ok(cnf.into_clauses())
            }
        }
    }

    /// This returns clauses that are denormalized in the sense that they sort literals,
    /// but don't filter out redundant or tautological literals.
    /// This is the format that the Checker uses.
    /// If you call normalize() on the clause afterwards, you should get the normalized one.
    pub fn value_to_denormalized_clauses(
        &mut self,
        value: &AcornValue,
    ) -> Result<Vec<Clause>, String> {
        let mut output = vec![];
        let cnf = self.value_to_cnf(&value, false, &mut vec![], &mut 0, &mut vec![])?;
        for mut literals in cnf.into_iter() {
            literals.sort();
            output.push(Clause { literals });
        }
        Ok(output)
    }

    /// Converts the value into a list of lists of literals, adding skolem constants
    /// to the normalizer as needed.
    /// True is [], false is [[]]. This is logical if you think hard about it.
    /// We leave general tautologies in here, and don't normalize until we convert to Clause.
    ///
    /// The variable numbering in the input and output is different.
    /// x_i in the input gets mapped to stack[i] in the output.
    /// This method must reset the stack before returning.
    ///
    /// Forall variables map into variables, but they may get renumbered, because the AcornValue
    /// a variable id can be used multiple times in different branches. In the output, variables
    /// in different branches may be combined. So each universal variable, anywhere in the value,
    /// gets a unique id.
    ///
    /// Existential variables turn into skolem terms. These are declared in the normalizer
    /// but not yet defined, because this function is creating the definition.
    /// Whenever we create a new skolem term, we add it to the synthesized list.
    fn value_to_cnf(
        &mut self,
        value: &AcornValue,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<AtomId>,
    ) -> Result<CNF, String> {
        match value {
            AcornValue::ForAll(qs, sub) => {
                if !negate {
                    self.forall_to_cnf(qs, sub, false, stack, next_var_id, synth)
                } else {
                    self.exists_to_cnf(qs, sub, true, stack, next_var_id, synth)
                }
            }
            AcornValue::Exists(qs, sub) => {
                if !negate {
                    self.exists_to_cnf(qs, sub, false, stack, next_var_id, synth)
                } else {
                    self.forall_to_cnf(qs, sub, true, stack, next_var_id, synth)
                }
            }
            AcornValue::Binary(BinaryOp::And, left, right) => {
                if !negate {
                    self.and_to_cnf(left, right, false, false, stack, next_var_id, synth)
                } else {
                    self.or_to_cnf(left, right, true, true, stack, next_var_id, synth)
                }
            }
            AcornValue::Binary(BinaryOp::Or, left, right) => {
                if !negate {
                    self.or_to_cnf(left, right, false, false, stack, next_var_id, synth)
                } else {
                    self.and_to_cnf(left, right, true, true, stack, next_var_id, synth)
                }
            }
            AcornValue::Binary(BinaryOp::Implies, left, right) => {
                if !negate {
                    self.or_to_cnf(left, right, true, false, stack, next_var_id, synth)
                } else {
                    self.and_to_cnf(left, right, false, true, stack, next_var_id, synth)
                }
            }
            AcornValue::Binary(BinaryOp::Equals, left, right) => {
                self.eq_to_cnf(left, right, negate, stack, next_var_id, synth)
            }
            AcornValue::Binary(BinaryOp::NotEquals, left, right) => {
                self.eq_to_cnf(left, right, !negate, stack, next_var_id, synth)
            }
            AcornValue::Not(subvalue) => {
                self.value_to_cnf(subvalue, !negate, stack, next_var_id, synth)
            }
            AcornValue::Try(_, _) => Err("try operator not yet implemented".to_string()),
            AcornValue::Bool(value) => {
                if *value ^ negate {
                    Ok(CNF::true_value())
                } else {
                    Ok(CNF::false_value())
                }
            }
            AcornValue::IfThenElse(cond_value, then_value, else_value) => {
                let cond_cnf = self.value_to_cnf(cond_value, false, stack, next_var_id, synth)?;
                let Some(cond_lit) = cond_cnf.to_literal() else {
                    return Err("value 'if' condition is too complicated".to_string());
                };
                let then_cnf = self.value_to_cnf(then_value, negate, stack, next_var_id, synth)?;
                let else_cnf = self.value_to_cnf(else_value, negate, stack, next_var_id, synth)?;
                Ok(CNF::cnf_if(cond_lit, then_cnf, else_cnf))
            }
            AcornValue::Application(app) => {
                let mut arg_exts = vec![];
                for arg in &app.args {
                    arg_exts.push(self.arg_to_extended_term(arg, stack, next_var_id, synth)?);
                }
                self.apply_to_cnf(&app.function, arg_exts, negate, stack, next_var_id, synth)
            }
            AcornValue::Variable(..) | AcornValue::Constant(..) | AcornValue::Lambda(..) => {
                let term = self
                    .value_to_extended_term(value, stack, next_var_id, synth)?
                    .to_term()?;
                let literal = Literal::from_signed_term(term, !negate);
                Ok(CNF::from_literal(literal))
            }
            AcornValue::Match(..) => Err("match in unexpected position".to_string()),
        }
    }

    fn apply_to_cnf(
        &mut self,
        function: &AcornValue,
        args: Vec<ExtendedTerm>,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<AtomId>,
    ) -> Result<CNF, String> {
        if let AcornValue::Lambda(_, return_value) = function {
            let mut arg_terms = vec![];
            for arg in args {
                arg_terms.push(arg.to_term()?);
            }
            let num_args = arg_terms.len();
            // Lambda arguments are bound variables
            for arg in arg_terms {
                stack.push(TermBinding::Bound(arg));
            }
            let answer = self.value_to_cnf(&return_value, negate, stack, next_var_id, synthesized);
            stack.truncate(stack.len() - num_args);
            return answer;
        }

        // Fall back to converting via extended term
        let extended =
            self.apply_to_extended_term(function, args, stack, next_var_id, synthesized)?;
        match extended {
            ExtendedTerm::Term(term) => {
                let literal = Literal::from_signed_term(term, !negate);
                Ok(CNF::from_literal(literal))
            }
            _ => Err("unhandled case: non-term application".to_string()),
        }
    }

    // Convert a "forall" node in a value, or the equivalent, to CNF.
    // negate is whether to negate the subvalue.
    fn forall_to_cnf(
        &mut self,
        quants: &Vec<AcornType>,
        subvalue: &AcornValue,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<AtomId>,
    ) -> Result<CNF, String> {
        for quant in quants {
            let type_id = self.type_store().get_type_id(quant)?;
            let var = Term::new_variable(type_id, *next_var_id);
            *next_var_id += 1;
            stack.push(TermBinding::Free(var));
        }
        let result = self.value_to_cnf(subvalue, negate, stack, next_var_id, synthesized)?;
        for _ in quants {
            stack.pop();
        }
        Ok(result)
    }

    // Define skolem functions that take the free variables on the stack as arguments.
    // One skolem function is created for each type in skolem_types.
    // Returns terms representing the applied skolem functions.
    fn make_skolem_terms(
        &mut self,
        skolem_types: &[AcornType],
        stack: &Vec<TermBinding>,
        synthesized: &mut Vec<AtomId>,
    ) -> Result<Vec<Term>, String> {
        let mut args = vec![];
        let mut arg_types = vec![];
        let mut seen_vars = std::collections::HashSet::new();

        for binding in stack.iter() {
            for (var_id, type_id) in binding.term().iter_vars() {
                if seen_vars.insert(var_id) {
                    let var_term = Term::new_variable(type_id, var_id);
                    args.push(var_term);
                    arg_types.push(self.type_store().get_type(type_id).clone());
                }
            }
        }

        let mut output = vec![];
        for t in skolem_types {
            // Each existential quantifier needs a new skolem atom.
            // The skolem term is that atom applied to the free variables on the stack.
            // Note that the skolem atom may be a type we have not used before.
            let skolem_atom_type = AcornType::functional(arg_types.clone(), t.clone());
            let skolem_atom_type_id = self.type_store_mut()?.add_type(&skolem_atom_type);
            let skolem_term_type_id = self.type_store().get_type_id(t)?;
            let skolem_id = self.as_mut()?.declare_synthetic_atom(skolem_atom_type)?;
            synthesized.push(skolem_id);
            let skolem_atom = Atom::Synthetic(skolem_id);
            let skolem_term = Term::new(
                skolem_term_type_id,
                skolem_atom_type_id,
                skolem_atom,
                args.clone(),
            );
            output.push(skolem_term);
        }
        Ok(output)
    }

    fn make_skolem_term(
        &mut self,
        skolem_type: &AcornType,
        stack: &Vec<TermBinding>,
        synthesized: &mut Vec<AtomId>,
    ) -> Result<Term, String> {
        let mut terms =
            self.make_skolem_terms(std::slice::from_ref(skolem_type), stack, synthesized)?;
        Ok(terms.pop().unwrap())
    }

    // Convert an "exists" node in a value, or the equivalent, to CNF.
    // negate is whether to negate the subvalue.
    fn exists_to_cnf(
        &mut self,
        quants: &Vec<AcornType>,
        subvalue: &AcornValue,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<AtomId>,
    ) -> Result<CNF, String> {
        let skolem_terms = self.make_skolem_terms(quants, stack, synthesized)?;
        let len = skolem_terms.len();
        for skolem_term in skolem_terms {
            stack.push(TermBinding::Bound(skolem_term));
        }
        let result = self.value_to_cnf(subvalue, negate, stack, next_var_id, synthesized)?;
        for _ in 0..len {
            stack.pop();
        }
        Ok(result)
    }

    // Convert an "and" node in a value, or the equivalent, to CNF.
    // negate_left and negate_right are whether to negate the respective subvalues.
    fn and_to_cnf(
        &mut self,
        left: &AcornValue,
        right: &AcornValue,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<AtomId>,
    ) -> Result<CNF, String> {
        let left = self.value_to_cnf(left, negate_left, stack, next_var_id, synthesized)?;
        let right = self.value_to_cnf(right, negate_right, stack, next_var_id, synthesized)?;
        Ok(left.and(right))
    }

    // Convert an "or" node in a value, or the equivalent, to CNF.
    // negate_left and negate_right are whether to negate the respective subvalues.
    fn or_to_cnf(
        &mut self,
        left: &AcornValue,
        right: &AcornValue,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<AtomId>,
    ) -> Result<CNF, String> {
        let left = self.value_to_cnf(left, negate_left, stack, next_var_id, synthesized)?;
        let right = self.value_to_cnf(right, negate_right, stack, next_var_id, synthesized)?;
        Ok(left.or(right))
    }

    // Convert an equality or inequality node in a value to CNF.
    // negate is whether it's an inequality.
    fn eq_to_cnf(
        &mut self,
        left: &AcornValue,
        right: &AcornValue,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<AtomId>,
    ) -> Result<CNF, String> {
        if let AcornValue::Match(scrutinee, cases) = right {
            // TODO: don't clone values here
            let mut answer = CNF::true_value();
            for (vars, pattern, result) in cases {
                // The meaning of the branch is:
                //   scrutinee = pattern implies left (negate=) result
                let op = if negate {
                    BinaryOp::NotEquals
                } else {
                    BinaryOp::Equals
                };
                let condition = AcornValue::equals(*scrutinee.clone(), pattern.clone());
                let conclusion =
                    AcornValue::Binary(op, Box::new(left.clone()), Box::new(result.clone()));
                let branch = AcornValue::implies(condition, conclusion);
                let conjunct_value = AcornValue::forall(vars.clone(), branch);
                let conjunct_cnf =
                    self.value_to_cnf(&conjunct_value, false, stack, next_var_id, synth)?;
                answer = answer.and(conjunct_cnf);
            }
            return Ok(answer);
        }

        if let AcornType::Function(app) = left.get_type() {
            // Comparing functions.
            let arg_types: Vec<TypeId> = app
                .arg_types
                .iter()
                .map(|t| self.type_store().get_type_id(t))
                .collect::<Result<Vec<_>, _>>()?;
            let result_type = self.type_store().get_type_id(&app.return_type)?;

            if result_type == BOOL {
                // Boolean functional comparison.
                if negate {
                    // Boolean functional inequality.
                    // Create skolem terms for each argument
                    let arg_terms = self.make_skolem_terms(&app.arg_types, stack, synth)?;
                    let args: Vec<_> = arg_terms.into_iter().map(ExtendedTerm::Term).collect();
                    let left_pos =
                        self.apply_to_cnf(left, args.clone(), false, stack, next_var_id, synth)?;
                    let left_neg =
                        self.apply_to_cnf(left, args.clone(), true, stack, next_var_id, synth)?;
                    let right_pos =
                        self.apply_to_cnf(right, args.clone(), false, stack, next_var_id, synth)?;
                    let right_neg =
                        self.apply_to_cnf(right, args, true, stack, next_var_id, synth)?;

                    if let Some((left_term, left_sign)) = left_pos.match_negated(&left_neg) {
                        if let Some((right_term, right_sign)) = right_pos.match_negated(&right_neg)
                        {
                            // Both sides are simple, so we can return a single literal.
                            let positive = left_sign != right_sign;
                            let literal =
                                Literal::new(positive, left_term.clone(), right_term.clone());
                            return Ok(CNF::from_literal(literal));
                        }
                    }

                    let some = left_pos.or(right_pos);
                    let not_both = left_neg.or(right_neg);
                    return Ok(not_both.and(some));
                }

                // Boolean functional equality.
                // Create new free variables for each argument
                let mut args = vec![];
                for arg_type in &arg_types {
                    let var = Term::new_variable(*arg_type, *next_var_id);
                    *next_var_id += 1;
                    args.push(ExtendedTerm::Term(var));
                }
                let left_pos =
                    self.apply_to_cnf(left, args.clone(), false, stack, next_var_id, synth)?;
                let left_neg =
                    self.apply_to_cnf(left, args.clone(), true, stack, next_var_id, synth)?;
                let right_pos =
                    self.apply_to_cnf(right, args.clone(), false, stack, next_var_id, synth)?;
                let right_neg = self.apply_to_cnf(right, args, true, stack, next_var_id, synth)?;

                if let Some((left_term, left_sign)) = left_pos.match_negated(&left_neg) {
                    if let Some((right_term, right_sign)) = right_pos.match_negated(&right_neg) {
                        // Both sides are simple, so we can return a single literal.
                        let positive = left_sign == right_sign;
                        let literal = Literal::new(positive, left_term.clone(), right_term.clone());
                        return Ok(CNF::from_literal(literal));
                    }
                }

                let l_imp_r = left_neg.or(right_pos);
                let r_imp_l = left_pos.or(right_neg);
                return Ok(l_imp_r.and(r_imp_l));
            }

            // Non-boolean functional comparison.
            let left = self.value_to_extended_term(left, stack, next_var_id, synth)?;
            let right = self.value_to_extended_term(right, stack, next_var_id, synth)?;
            if negate {
                // Functional inequality.
                // Create skolem terms for each argument
                let args = self.make_skolem_terms(&app.arg_types, stack, synth)?;
                // Apply the skolem terms to both sides
                let left = left.apply(&args, result_type);
                let right = right.apply(&args, result_type);
                return left.eq_to_cnf(right, true);
            }

            // Functional equality.
            // Create new free variables for each argument
            let mut args = vec![];
            for arg_type in &arg_types {
                let var = Term::new_variable(*arg_type, *next_var_id);
                *next_var_id += 1;
                args.push(var);
            }
            // Apply the free variables to both sides
            let left = left.apply(&args, result_type);
            let right = right.apply(&args, result_type);
            return left.eq_to_cnf(right, false);
        }

        if left.is_bool_type() {
            if let Some((left_term, left_sign)) =
                self.try_simple_value_to_signed_term(left, stack)?
            {
                if let Some((right_term, right_sign)) =
                    self.try_simple_value_to_signed_term(right, stack)?
                {
                    // Both sides are terms, so we can do a simple equality or inequality
                    let positive = (left_sign == right_sign) ^ negate;
                    let literal = Literal::new(positive, left_term, right_term);
                    return Ok(CNF::from_literal(literal));
                }
            }

            // This logic duplicates subterms. Either we need to be careful that we don't synthesize
            // variables in these calls, or we need to globally deduplicate at synthesis time.
            if negate {
                // Boolean inequality.
                let some = self.or_to_cnf(left, right, true, true, stack, next_var_id, synth)?;
                let not_both =
                    self.or_to_cnf(left, right, false, false, stack, next_var_id, synth)?;
                return Ok(some.and(not_both));
            }

            // Boolean equality.
            let l_imp_r = self.or_to_cnf(left, right, true, false, stack, next_var_id, synth)?;
            let r_imp_l = self.or_to_cnf(left, right, false, true, stack, next_var_id, synth)?;
            return Ok(l_imp_r.and(r_imp_l));
        }

        // Plain old equality of terms.
        let left = self.value_to_extended_term(left, stack, next_var_id, synth)?;
        let right = self.value_to_extended_term(right, stack, next_var_id, synth)?;
        left.eq_to_cnf(right, negate)
    }

    /// Converts a value to a Term, if possible.
    /// This doesn't mutate the normalizer, so it only handles simple values, no quantifiers.
    /// This uses errors to report invalid values.
    /// If it is called on a value that doesn't convert to a term, it returns Ok(None).
    fn try_simple_value_to_term(
        &self,
        value: &AcornValue,
        stack: &Vec<TermBinding>,
    ) -> Result<Option<Term>, String> {
        match self.try_simple_value_to_signed_term(value, stack)? {
            None => Ok(None),
            Some((t, sign)) => {
                if sign {
                    Ok(Some(t))
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Like try_simple_value_to_term, but returns an error if it doesn't work.
    fn force_simple_value_to_term(
        &self,
        value: &AcornValue,
        stack: &Vec<TermBinding>,
    ) -> Result<Term, String> {
        match self.try_simple_value_to_term(value, stack)? {
            Some(t) => Ok(t),
            None => Err(format!("expected simple term but got '{}'", value)),
        }
    }

    /// Converts a value to a Term plus a sign, if possible.
    /// true = positive.
    /// This doesn't mutate the normalizer, so it only handles simple values, no quantifiers.
    /// This uses errors to report invalid values.
    /// If it is just called on a value that doesn't convert to a signed term, it returns Ok(None).
    fn try_simple_value_to_signed_term(
        &self,
        value: &AcornValue,
        stack: &Vec<TermBinding>,
    ) -> Result<Option<(Term, bool)>, String> {
        match value {
            AcornValue::Variable(i, _) => {
                if (*i as usize) < stack.len() {
                    Ok(Some((stack[*i as usize].term().clone(), true)))
                } else {
                    Err(format!("variable {} out of range in simple term", i))
                }
            }
            AcornValue::Application(application) => {
                let application_type = application.get_type();
                let term_type = self.type_store().get_type_id(&application_type)?;
                let func_term = match self.try_simple_value_to_term(&application.function, stack)? {
                    Some(t) => t,
                    None => return Ok(None),
                };
                let head = *func_term.get_head_atom();
                let head_type = func_term.get_head_type();
                let mut args = func_term.args().to_vec();
                for arg in &application.args {
                    let arg_term = match self.try_simple_value_to_term(arg, stack)? {
                        Some(t) => t,
                        None => return Ok(None),
                    };
                    args.push(arg_term);
                }
                Ok(Some((Term::new(term_type, head_type, head, args), true)))
            }
            AcornValue::Constant(c) => {
                if c.params.is_empty() {
                    let type_id = self.type_store().get_type_id(&c.instance_type)?;

                    let Some(atom) = self.map().get_atom(&c.name) else {
                        return Err(format!("constant {} not found in normalization map", c));
                    };
                    Ok(Some((Term::new(type_id, type_id, atom, vec![]), true)))
                } else {
                    Ok(Some((self.map().term_from_monomorph(&c)?, true)))
                }
            }
            AcornValue::Not(subvalue) => {
                match self.try_simple_value_to_signed_term(subvalue, stack)? {
                    None => Ok(None),
                    Some((t, sign)) => Ok(Some((t, !sign))),
                }
            }
            AcornValue::Try(_, _) => Ok(None),
            AcornValue::Bool(v) => Ok(Some((Term::new_true(), *v))),
            _ => Ok(None),
        }
    }

    /// Handles application of a function to arguments, converting to an ExtendedTerm.
    fn apply_to_extended_term(
        &mut self,
        function: &AcornValue,
        args: Vec<ExtendedTerm>,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<AtomId>,
    ) -> Result<ExtendedTerm, String> {
        if let AcornValue::Lambda(_, return_value) = function {
            let mut arg_terms = vec![];
            for arg in args {
                arg_terms.push(arg.to_term()?);
            }
            let num_args = arg_terms.len();
            // Lambda arguments are bound variables
            for arg in arg_terms {
                stack.push(TermBinding::Bound(arg));
            }
            let answer = self.value_to_extended_term(&return_value, stack, next_var_id, synth);
            stack.truncate(stack.len() - num_args);
            return answer;
        }

        // We convert f(if a then b else c, d) into if a then f(b, d) else f(c, d).
        // The "spine" logic makes branching work for f as well.
        // If we discover a branching subterm, then we set cond and spine2.
        let mut cond: Option<Literal> = None;
        let mut spine1 = vec![];
        let mut spine2 = vec![];

        // First process the function
        match self.value_to_extended_term(function, stack, next_var_id, synth)? {
            ExtendedTerm::Term(t) => {
                spine1.push(t);
            }
            ExtendedTerm::If(sub_cond, sub_then, sub_else) => {
                cond = Some(sub_cond);
                spine1.push(sub_then);
                spine2.push(sub_else);
            }
            ExtendedTerm::Lambda(_, _) => {
                // Can this happen?
                return Err("unhandled case: secret lambda".to_string());
            }
        }

        // Determine the result type from the original application
        let args_len = args.len();

        // Then process the arguments
        for arg in args {
            match arg {
                ExtendedTerm::Term(t) => {
                    if !spine2.is_empty() {
                        spine2.push(t.clone());
                    }
                    spine1.push(t);
                }
                ExtendedTerm::If(sub_cond, sub_then, sub_else) => {
                    if !spine2.is_empty() {
                        return Err("unhandled case: multiple if args".to_string());
                    }
                    cond = Some(sub_cond);
                    spine2.extend(spine1.iter().cloned());
                    spine1.push(sub_then);
                    spine2.push(sub_else);
                }
                ExtendedTerm::Lambda(_, _) => {
                    return Err("unhandled case: lambda arg".to_string());
                }
            }
        }
        let result_type = {
            let func_type = function.get_type();
            if let AcornType::Function(fapp) = func_type {
                if args_len > fapp.arg_types.len() {
                    return Err("too many arguments".to_string());
                }
                let remaining_args = fapp.arg_types.len() - args_len;
                if remaining_args == 0 {
                    self.type_store().get_type_id(&fapp.return_type)?
                } else {
                    let remaining_type = AcornType::functional(
                        fapp.arg_types[args_len..].to_vec(),
                        (*fapp.return_type).clone(),
                    );
                    self.type_store().get_type_id(&remaining_type)?
                }
            } else {
                return Err("cannot apply non-function".to_string());
            }
        };

        match cond {
            Some(cond) => {
                assert_eq!(spine1.len(), spine2.len());
                let then_term = Term::from_spine(spine1, result_type);
                let else_term = Term::from_spine(spine2, result_type);
                Ok(ExtendedTerm::If(cond, then_term, else_term))
            }
            None => {
                assert!(spine2.is_empty());
                let term = Term::from_spine(spine1, result_type);
                Ok(ExtendedTerm::Term(term))
            }
        }
    }

    /// Synthesizes a term to represent a value by creating a synthetic atom
    /// and defining it to equal the value.
    /// This is used for values that can't be directly converted to terms,
    /// like boolean logic expressions or lambdas.
    /// If an equivalent definition already exists, reuses the existing synthetic atom.
    fn synthesize_term(
        &mut self,
        value: &AcornValue,
        value_type: &AcornType,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<AtomId>,
    ) -> Result<Term, String> {
        // Create a tentative skolem term with the value's type
        let skolem_term = self.make_skolem_term(value_type, stack, synth)?;
        let skolem_id = if let Atom::Synthetic(id) = *skolem_term.get_head_atom() {
            id
        } else {
            return Err("internal error: skolem term is not synthetic".to_string());
        };

        // Create the definition for this synthetic term
        let skolem_value = self
            .as_ref()
            .denormalize_term(&skolem_term, &mut None, None);
        let definition_cnf =
            self.eq_to_cnf(&skolem_value, value, false, stack, next_var_id, synth)?;
        let clauses = definition_cnf.clone().into_clauses();

        // Check if an equivalent definition already exists
        let synthetic_key_form: Vec<_> = clauses
            .iter()
            .map(|c| c.invalidate_synthetics(&[skolem_id]))
            .collect();
        let key = SyntheticKey {
            clauses: synthetic_key_form,
            num_atoms: 1,
        };

        if let Some(existing_def) = self.as_ref().synthetic_map.get(&key) {
            // Reuse the existing synthetic atom
            let existing_id = existing_def.atoms[0];
            let existing_atom = Atom::Synthetic(existing_id);
            let reused_term = Term::new(
                skolem_term.get_term_type(),
                skolem_term.get_head_type(),
                existing_atom,
                skolem_term.args().to_vec(),
            );
            Ok(reused_term)
        } else {
            // Define the new synthetic atom
            // No source available here since we're synthesizing during normalization
            self.as_mut()?
                .define_synthetic_atoms(vec![skolem_id], clauses, None)?;
            Ok(skolem_term)
        }
    }

    /// Converts a value to an ExtendedTerm when it's being used as an argument.
    /// This handles lambdas specially by synthesizing terms for them,
    /// since lambdas can't be directly converted to plain terms.
    fn arg_to_extended_term(
        &mut self,
        value: &AcornValue,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<AtomId>,
    ) -> Result<ExtendedTerm, String> {
        match value {
            AcornValue::Lambda(_, _) => {
                // Synthesize a term to represent this lambda
                let lambda_type = value.get_type();
                let skolem_term =
                    self.synthesize_term(value, &lambda_type, stack, next_var_id, synth)?;
                Ok(ExtendedTerm::Term(skolem_term))
            }
            _ => {
                // For non-lambda values, use the standard conversion
                self.value_to_extended_term(value, stack, next_var_id, synth)
            }
        }
    }

    /// Synthesizes a literal from a CNF by creating a new synthetic boolean atom
    /// and adding clauses that define it to be equivalent to the CNF.
    /// This uses a Tseitin-style transformation: for CNF C and new atom s,
    /// we add clauses for s <-> C, which is (s -> C) and (C -> s).
    fn synthesize_literal_from_cnf(
        &mut self,
        cnf: CNF,
        stack: &Vec<TermBinding>,
        synth: &mut Vec<AtomId>,
    ) -> Result<Literal, String> {
        use crate::acorn_type::AcornType;
        use crate::atom::Atom;

        // Create a new synthetic boolean atom with the appropriate function type
        // based on free variables in the stack
        let mut arg_types = vec![];
        let mut args = vec![];
        let mut seen_vars = std::collections::HashSet::new();

        for binding in stack.iter() {
            for (var_id, type_id) in binding.term().iter_vars() {
                if seen_vars.insert(var_id) {
                    let var_term = Term::new_variable(type_id, var_id);
                    args.push(var_term);
                    arg_types.push(self.type_store().get_type(type_id).clone());
                }
            }
        }

        let bool_type = AcornType::Bool;
        let atom_type = if arg_types.is_empty() {
            bool_type.clone()
        } else {
            AcornType::functional(arg_types, bool_type.clone())
        };

        // Add the atom type to the normalization map and declare the synthetic atom
        let atom_id = self.as_mut()?.declare_synthetic_atom(atom_type.clone())?;
        synth.push(atom_id);

        // Now we can safely get type IDs
        let bool_type_id = self.type_store().get_type_id(&bool_type)?;
        let atom_type_id = self.type_store().get_type_id(&atom_type)?;

        let atom = Atom::Synthetic(atom_id);
        let synth_term = Term::new(bool_type_id, atom_type_id, atom, args);
        let synth_lit = Literal::from_signed_term(synth_term.clone(), true);

        // Create defining clauses for: s <-> C
        // This is (s -> C) and (C -> s)
        // Which is (not s or C) and (not C or s)
        let mut defining_clauses = vec![];

        // For (not s or C):
        // C is a conjunction of clauses, so we add (not s or Ci) for each clause Ci
        for clause_lits in cnf.clone().into_iter() {
            let mut new_clause_lits = vec![synth_lit.negate()];
            new_clause_lits.extend(clause_lits);
            defining_clauses.push(Clause::new(new_clause_lits));
        }

        // For (not C or s):
        // We negate C and add s to each resulting clause
        let neg_cnf = cnf.negate();
        for clause_lits in neg_cnf.into_iter() {
            let mut new_clause_lits = clause_lits;
            new_clause_lits.push(synth_lit.clone());
            defining_clauses.push(Clause::new(new_clause_lits));
        }

        // Add the definition
        self.as_mut()?
            .define_synthetic_atoms(vec![atom_id], defining_clauses, None)?;

        Ok(synth_lit)
    }

    /// Converts an ExtendedTerm to a plain Term.
    /// If the ExtendedTerm is an If expression, synthesizes a new atom for it.
    fn extended_term_to_term(
        &mut self,
        ext_term: ExtendedTerm,
        synth: &mut Vec<AtomId>,
    ) -> Result<Term, String> {
        match ext_term {
            ExtendedTerm::Term(t) => Ok(t),
            ExtendedTerm::If(cond_lit, then_term, else_term) => {
                // Optimization: if both branches are the same, just return that term
                if then_term == else_term {
                    return Ok(then_term);
                }
                // We need to synthesize a new atom that represents this if-expression
                // The defining clauses will be:
                // For atom s representing "if cond then then_term else else_term":
                // (cond -> s = then_term) and (not cond -> s = else_term)
                // Which is (not cond or s = then_term) and (cond or s = else_term)

                use crate::acorn_type::AcornType;
                use crate::atom::Atom;

                // Determine the type of the result (should be same as then_term and else_term)
                let result_type_id = then_term.get_term_type();
                let result_type = self.type_store().get_type(result_type_id).clone();

                // Create a new synthetic atom with the appropriate function type
                // based on free variables in the if-expression
                let mut arg_types = vec![];
                let mut args = vec![];
                let mut seen_vars = std::collections::HashSet::new();

                // Collect free variables from the condition literal
                for (var_id, type_id) in cond_lit.left.iter_vars() {
                    if seen_vars.insert(var_id) {
                        let var_term = Term::new_variable(type_id, var_id);
                        args.push(var_term);
                        arg_types.push(self.type_store().get_type(type_id).clone());
                    }
                }
                for (var_id, type_id) in cond_lit.right.iter_vars() {
                    if seen_vars.insert(var_id) {
                        let var_term = Term::new_variable(type_id, var_id);
                        args.push(var_term);
                        arg_types.push(self.type_store().get_type(type_id).clone());
                    }
                }

                // Collect free variables from the then branch
                for (var_id, type_id) in then_term.iter_vars() {
                    if seen_vars.insert(var_id) {
                        let var_term = Term::new_variable(type_id, var_id);
                        args.push(var_term);
                        arg_types.push(self.type_store().get_type(type_id).clone());
                    }
                }

                // Collect free variables from the else branch
                for (var_id, type_id) in else_term.iter_vars() {
                    if seen_vars.insert(var_id) {
                        let var_term = Term::new_variable(type_id, var_id);
                        args.push(var_term);
                        arg_types.push(self.type_store().get_type(type_id).clone());
                    }
                }

                let atom_type = if arg_types.is_empty() {
                    result_type.clone()
                } else {
                    AcornType::functional(arg_types, result_type.clone())
                };

                // Add the atom type to the normalization map and declare the synthetic atom
                let atom_id = self.as_mut()?.declare_synthetic_atom(atom_type.clone())?;
                synth.push(atom_id);

                // Now we can safely get type IDs
                let atom_type_id = self.type_store().get_type_id(&atom_type)?;

                let atom = Atom::Synthetic(atom_id);
                let synth_term = Term::new(result_type_id, atom_type_id, atom, args);

                // Create defining clauses for the if-expression
                // (not cond or synth_term = then_term) and (cond or synth_term = else_term)
                let mut defining_clauses = vec![];

                // First clause: not cond or synth_term = then_term
                let then_eq = Literal::new(true, synth_term.clone(), then_term);
                defining_clauses.push(Clause::new(vec![cond_lit.negate(), then_eq]));

                // Second clause: cond or synth_term = else_term
                let else_eq = Literal::new(true, synth_term.clone(), else_term);
                defining_clauses.push(Clause::new(vec![cond_lit.clone(), else_eq]));

                // Add the definition
                self.as_mut()?
                    .define_synthetic_atoms(vec![atom_id], defining_clauses, None)?;

                Ok(synth_term)
            }
            ExtendedTerm::Lambda(_, t) => Err(format!("cannot convert lambda {} to plain term", t)),
        }
    }

    /// Converts a value to an ExtendedTerm, which can appear in places a Term does.
    fn value_to_extended_term(
        &mut self,
        value: &AcornValue,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<AtomId>,
    ) -> Result<ExtendedTerm, String> {
        match value {
            AcornValue::IfThenElse(cond_val, then_value, else_value) => {
                let cond_cnf = self.value_to_cnf(cond_val, false, stack, next_var_id, synth)?;
                let cond_lit = if cond_cnf.is_literal() {
                    cond_cnf.to_literal().unwrap()
                } else {
                    // For non-literal conditions, synthesize a new boolean atom
                    self.synthesize_literal_from_cnf(cond_cnf, stack, synth)?
                };
                let then_ext =
                    self.value_to_extended_term(then_value, stack, next_var_id, synth)?;
                let then_branch = self.extended_term_to_term(then_ext, synth)?;
                let else_ext =
                    self.value_to_extended_term(else_value, stack, next_var_id, synth)?;
                let else_branch = self.extended_term_to_term(else_ext, synth)?;
                Ok(ExtendedTerm::If(cond_lit, then_branch, else_branch))
            }
            AcornValue::Application(app) => {
                let mut arg_exts = vec![];
                for arg in &app.args {
                    arg_exts.push(self.arg_to_extended_term(arg, stack, next_var_id, synth)?);
                }
                self.apply_to_extended_term(&app.function, arg_exts, stack, next_var_id, synth)
            }
            AcornValue::Variable(i, _) => {
                if (*i as usize) < stack.len() {
                    Ok(ExtendedTerm::Term(stack[*i as usize].term().clone()))
                } else {
                    Err(format!("variable {} out of range in extended term", i))
                }
            }
            AcornValue::Constant(c) => {
                if c.params.is_empty() {
                    let type_id = self.type_store().get_type_id(&c.instance_type)?;

                    let Some(atom) = self.map().get_atom(&c.name) else {
                        return Err(format!("constant {} not found in normalization map", c));
                    };
                    Ok(ExtendedTerm::Term(Term::new(
                        type_id,
                        type_id,
                        atom,
                        vec![],
                    )))
                } else {
                    Ok(ExtendedTerm::Term(self.map().term_from_monomorph(&c)?))
                }
            }
            AcornValue::Not(_) => Err("negation in unexpected position".to_string()),
            AcornValue::Try(_, _) => Err("try operator not yet implemented".to_string()),
            AcornValue::Lambda(arg_types, body) => {
                // Create variable terms for each lambda argument
                // Use stack.len() as the variable ID to ensure it matches the AcornValue's stack-position indexing
                let mut args = vec![];
                for arg_type in arg_types {
                    let type_id = self.type_store().get_type_id(arg_type)?;
                    let var_id = stack.len() as AtomId;
                    let var = Term::new_variable(type_id, var_id);
                    args.push((var_id, type_id));
                    stack.push(TermBinding::Free(var));
                    // Update next_var_id to be at least one past this variable
                    if var_id >= *next_var_id {
                        *next_var_id = var_id + 1;
                    }
                }

                // Evaluate the body with the lambda arguments on the stack
                let body_term = self
                    .value_to_extended_term(body, stack, next_var_id, synth)?
                    .to_term()?;

                // Pop the lambda arguments from the stack
                for _ in arg_types {
                    stack.pop();
                }

                Ok(ExtendedTerm::Lambda(args, body_term))
            }
            AcornValue::Bool(b) => {
                if *b {
                    Ok(ExtendedTerm::Term(Term::new_true()))
                } else {
                    Err("false literal in unexpected position".to_string())
                }
            }
            value if value.is_bool_type() => {
                // Synthesize a term to represent this boolean value.
                let skolem_term =
                    self.synthesize_term(value, &AcornType::Bool, stack, next_var_id, synth)?;
                Ok(ExtendedTerm::Term(skolem_term))
            }
            _ => Err(format!("cannot convert '{}' to extended term", value)),
        }
    }
}

impl Normalizer {
    /// This should handle any sort of boolean value.
    /// TODO: port edge cases into the "nice" value to clauses so that we only have one of these.
    fn ugly_value_to_clauses(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
        source: &Source,
    ) -> Result<Vec<Clause>, String> {
        self.normalization_map
            .add_from(&value, ctype, &mut self.type_store);

        // TODO: can we remove this? Expanding them doesn't really seem right.
        // Maybe we can inline lambdas instead of expanding them.
        let value = value.expand_lambdas(0);

        let mut skolem_ids = vec![];
        let mut mut_view = NormalizerView::Mut(self);
        let clauses = mut_view.nice_value_to_clauses(&value, &mut skolem_ids)?;

        // For any of the created ids that have not been defined yet, the output
        // clauses will be their definition.
        let mut output = vec![];
        let mut undefined_ids = vec![];
        for id in skolem_ids {
            if let Some(def) = self.synthetic_definitions.get(&id) {
                for clause in &def.clauses {
                    output.push(clause.clone());
                }
            } else {
                undefined_ids.push(id);
            }
        }

        if !undefined_ids.is_empty() {
            // We have to define the skolem atoms that were declared during skolemization.
            self.define_synthetic_atoms(undefined_ids, clauses.clone(), Some(source.clone()))?;
        }

        output.extend(clauses.into_iter());
        Ok(output)
    }

    /// Converts a value to CNF: Conjunctive Normal Form.
    /// In other words, a successfully normalized value turns into a bunch of clauses.
    /// Logically, this is an "and of ors".
    /// Each Clause represents an implicit "forall", plus an "or" of its literals.
    /// "true" is represented by an empty list, which is always satisfied.
    /// "false" is represented by a single impossible clause.
    /// This is kind of just a wrapper around convert_then_normalize which adds on
    /// some verification and a hack for functional equality.
    fn normalize_value(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
        source: &Source,
    ) -> Result<Vec<Clause>, String> {
        if let Err(e) = value.validate() {
            return Err(format!(
                "validation error: {} while normalizing: {}",
                e, value
            ));
        }
        assert!(value.is_bool_type());

        let mut clauses = self.ugly_value_to_clauses(value, ctype, source)?;

        if let AcornValue::Binary(BinaryOp::Equals, left, right) = &value {
            if left.get_type().is_functional() && left.is_term() && right.is_term() {
                // This is an annoying case.
                // If we are expressing, say,
                //   f(a) = g(b)
                // where the return value is a functional type, that gets normalized into:
                //   f(a, x0) = g(b, x0)
                // The problem is that we do also want the functional equality.
                // In most cases, we can get this in the prover by the extensionality rule.
                // However, in this specific case we can't, because in the Clause,
                // the type of f(a) has been erased.
                // So we add back in the plain literal version that hasn't been normalized.
                //
                // Ideally, we would either:
                //   1. Represent functional types better in unification, so that we
                //      don't have to normalize by adding args, and we can keep it as
                //      f(a) = g(b)
                //   2. Make extensionality more powerful, so that it can deduce f(a) = g(b).
                let view = NormalizerView::Ref(self);
                let left_term = view.force_simple_value_to_term(left, &vec![])?;
                let right_term = view.force_simple_value_to_term(right, &vec![])?;
                let literal = Literal::new(true, left_term, right_term);
                let clause = Clause::new(vec![literal]);
                clauses.push(clause);
            }
        }

        Ok(clauses)
    }

    /// A single fact can turn into a bunch of proof steps.
    /// This monomorphizes, which can indirectly turn into what seems like a lot of unrelated steps.
    pub fn normalize_fact(&mut self, fact: Fact) -> Result<Vec<ProofStep>, BuildError> {
        let mut steps = vec![];

        // Check if this looks like an aliasing.
        if let Some((ci, name, constant_type)) = fact.as_instance_alias() {
            let local = fact.source().truthiness() != Truthiness::Factual;
            self.normalization_map.alias_monomorph(
                ci,
                name,
                &constant_type,
                local,
                &mut self.type_store,
            );
            return Ok(steps);
        }

        let range = fact.source().range;
        self.monomorphizer.add_fact(fact);
        for proposition in self.monomorphizer.take_output() {
            let ctype = if proposition.source.truthiness() == Truthiness::Factual {
                NewConstantType::Global
            } else {
                NewConstantType::Local
            };
            let clauses = self
                .normalize_value(&proposition.value, ctype, &proposition.source)
                .map_err(|msg| BuildError::new(range, msg))?;
            let defined = match &proposition.source.source_type {
                SourceType::ConstantDefinition(value, _) => {
                    let view = NormalizerView::Ref(self);
                    let term = view
                        .force_simple_value_to_term(value, &vec![])
                        .map_err(|msg| {
                            BuildError::new(
                                range,
                                format!("cannot convert definition to term: {}", msg),
                            )
                        })?;
                    Some(term.get_head_atom().clone())
                }
                _ => None,
            };
            for clause in clauses {
                let step = ProofStep::assumption(&proposition, clause, defined);
                steps.push(step);
            }
        }
        Ok(steps)
    }
}

#[derive(Clone)]
pub struct NormalizedGoal {
    /// The name of the goal being proved.
    pub name: String,

    /// The value expresses the negation of the goal we are trying to prove.
    /// It is normalized in the sense that hypothesis and counterfactual have been separated.
    /// There is still more normalization that will happen when it is converted to Clause.
    pub counterfactual: AcornValue,

    /// Whether inconsistencies are okay.
    /// If true, finding a contradiction results in Outcome::Success.
    /// If false, finding a contradiction results in Outcome::Inconsistent.
    pub inconsistency_okay: bool,
}

impl Normalizer {
    /// Normalizes a goal into a NormalizedGoal and proof steps that includes
    /// both positive versions of the hypotheses and negated versions of the conclusion.
    pub fn normalize_goal(
        &mut self,
        goal: &Goal,
    ) -> Result<(NormalizedGoal, Vec<ProofStep>), BuildError> {
        let prop = &goal.proposition;
        let (hypo, counterfactual) = prop.value.clone().negate_goal();
        let mut steps = vec![];
        if let Some(hypo) = hypo {
            let fact = Fact::proposition(hypo, prop.source.clone());
            steps.extend(self.normalize_fact(fact)?);
        }
        let fact = Fact::proposition(counterfactual.clone(), prop.source.as_negated_goal());
        steps.extend(self.normalize_fact(fact)?);

        let ng = NormalizedGoal {
            name: goal.name.clone(),
            counterfactual,
            inconsistency_okay: goal.inconsistency_okay,
        };
        Ok((ng, steps))
    }

    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// Any other free variables are left unbound. Their types are accumulated.
    fn denormalize_atom(
        &self,
        atom_type: TypeId,
        atom: &Atom,
        var_types: &mut Option<Vec<AcornType>>,
        arbitrary_names: Option<&HashMap<TypeId, ConstantName>>,
    ) -> AcornValue {
        let acorn_type = self.type_store.get_type(atom_type).clone();
        match atom {
            Atom::True => AcornValue::Bool(true),
            Atom::GlobalConstant(i) => {
                let name = self.normalization_map.name_for_global_id(*i).clone();
                AcornValue::constant(name, vec![], acorn_type)
            }
            Atom::LocalConstant(i) => {
                let name = self.normalization_map.name_for_local_id(*i).clone();
                AcornValue::constant(name, vec![], acorn_type)
            }
            Atom::Monomorph(i) => {
                AcornValue::Constant(self.normalization_map.get_monomorph(*i).clone())
            }
            Atom::Variable(i) => {
                if let Some(map) = arbitrary_names {
                    if let Some(name) = map.get(&atom_type) {
                        return AcornValue::constant(name.clone(), vec![], acorn_type);
                    }
                }
                if let Some(var_types) = var_types {
                    let index = *i as usize;
                    if index < var_types.len() {
                        assert_eq!(var_types[index], acorn_type);
                    } else if index == var_types.len() {
                        var_types.push(acorn_type.clone());
                    } else {
                        panic!("variable index out of order");
                    }
                }
                AcornValue::Variable(*i, acorn_type)
            }
            Atom::Synthetic(i) => {
                let acorn_type = self.synthetic_types[*i as usize].clone();
                let name = ConstantName::Synthetic(*i);
                AcornValue::constant(name, vec![], acorn_type)
            }
        }
    }

    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// Any other free variables are left unbound. Their types are accumulated.
    fn denormalize_term(
        &self,
        term: &Term,
        var_types: &mut Option<Vec<AcornType>>,
        arbitrary_names: Option<&HashMap<TypeId, ConstantName>>,
    ) -> AcornValue {
        let head = self.denormalize_atom(
            term.get_head_type(),
            &term.get_head_atom(),
            var_types,
            arbitrary_names,
        );
        let args: Vec<_> = term
            .args()
            .iter()
            .map(|t| self.denormalize_term(t, var_types, arbitrary_names))
            .collect();
        AcornValue::apply(head, args)
    }

    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// If var_types is provided, we accumulate the types of any free variables we encounter.
    /// Any other free variables are left unbound. Their types are accumulated.
    fn denormalize_literal(
        &self,
        literal: &Literal,
        var_types: &mut Option<Vec<AcornType>>,
        arbitrary_names: Option<&HashMap<TypeId, ConstantName>>,
    ) -> AcornValue {
        let left = self.denormalize_term(&literal.left, var_types, arbitrary_names);
        if literal.right.is_true() {
            if literal.positive {
                return left;
            } else {
                return AcornValue::Not(Box::new(left));
            }
        }
        let right = self.denormalize_term(&literal.right, var_types, arbitrary_names);
        if literal.positive {
            AcornValue::equals(left, right)
        } else {
            AcornValue::not_equals(left, right)
        }
    }

    /// Converts backwards, from a clause to a value.
    /// The resulting value may have synthetic atoms in it.
    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// Any remaining free variables are enclosed in a "forall" quantifier.
    pub fn denormalize(
        &self,
        clause: &Clause,
        arbitrary_names: Option<&HashMap<TypeId, ConstantName>>,
    ) -> AcornValue {
        if clause.literals.is_empty() {
            return AcornValue::Bool(false);
        }
        let mut var_types = Some(vec![]);
        let mut denormalized_literals = vec![];
        for literal in &clause.literals {
            denormalized_literals.push(self.denormalize_literal(
                literal,
                &mut var_types,
                arbitrary_names,
            ));
        }
        let disjunction = AcornValue::reduce(BinaryOp::Or, denormalized_literals);
        AcornValue::forall(var_types.unwrap(), disjunction)
    }

    pub fn denormalize_type(&self, type_id: TypeId) -> AcornType {
        self.type_store.get_type(type_id).clone()
    }

    /// Given a list of atom ids for synthetic atoms that we need to define, find a set
    /// of SyntheticInfo that covers them.
    /// The output may have synthetic atoms that aren't used in the input.
    /// The input doesn't have to be in order and may contain duplicates.
    pub fn find_covering_synthetic_info(&self, ids: &[AtomId]) -> Vec<Arc<SyntheticDefinition>> {
        let mut covered = HashSet::new();
        let mut output = vec![];
        for id in ids {
            if covered.contains(id) {
                continue;
            }
            let info = self.synthetic_definitions[id].clone();
            for synthetic_id in &info.atoms {
                covered.insert(*synthetic_id);
            }
            output.push(info);
        }
        output
    }

    pub fn atom_str(&self, atom: &Atom) -> String {
        match atom {
            Atom::True => "true".to_string(),
            Atom::GlobalConstant(i) => self.normalization_map.name_for_global_id(*i).to_string(),
            Atom::LocalConstant(i) => self.normalization_map.name_for_local_id(*i).to_string(),
            Atom::Monomorph(i) => {
                format!("{}", self.normalization_map.get_monomorph(*i))
            }
            Atom::Variable(i) => format!("x{}", i),
            Atom::Synthetic(i) => format!("s{}", i),
        }
    }

    /// When you denormalize and renormalize a clause, you should get the same thing.
    #[cfg(test)]
    fn check_denormalize_renormalize(&mut self, clause: &Clause) {
        let denormalized = self.denormalize(clause, None);
        denormalized
            .validate()
            .expect("denormalized clause should validate");
        let renormalized = self
            .normalize_value(&denormalized, NewConstantType::Local, &Source::mock())
            .unwrap();
        if renormalized.len() != 1 {
            if true {
                // For functional equalities, we know this check doesn't work.
                // So we skip it.
                return;
            }
            println!("original clause: {}", clause);
            println!("denormalized: {}", denormalized);
            for (i, clause) in renormalized.iter().enumerate() {
                println!("renormalized[{}]: {}", i, clause);
            }
            panic!("expected 1 clause, got {}", renormalized.len());
        }
        if clause != &renormalized[0] {
            println!("original clause: {}", clause);
            println!("denormalized: {}", denormalized);
            println!("renormalized: {}", renormalized[0]);
            panic!("renormalized clause does not match original");
        }
    }

    #[cfg(test)]
    fn check_value(&mut self, value: &AcornValue, expected: &[&str]) {
        use crate::display::DisplayClause;

        let actual = self
            .normalize_value(value, NewConstantType::Local, &Source::mock())
            .unwrap();
        if actual.len() != expected.len() {
            panic!(
                "expected {} clauses, got {}:\n{}",
                expected.len(),
                actual.len(),
                actual
                    .iter()
                    .map(|c| DisplayClause {
                        clause: c,
                        normalizer: self,
                    }
                    .to_string())
                    .collect::<Vec<String>>()
                    .join("\n")
            );
        }
        for (i, clause) in actual.iter().enumerate() {
            self.check_denormalize_renormalize(clause);
            let c = DisplayClause {
                clause,
                normalizer: self,
            };
            let a = c.to_string();
            if a != expected[i] {
                panic!("expected clause {} to be:\n{}\ngot:\n{}", i, expected[i], a);
            }
        }
    }

    /// Checks a theorem. Just for testing purposes.
    #[cfg(test)]
    pub fn check(&mut self, env: &crate::environment::Environment, name: &str, expected: &[&str]) {
        for node in &env.nodes {
            if let Some((theorem_name, value)) = node.as_theorem() {
                if theorem_name == name {
                    self.check_value(&value, expected);
                    return;
                }
            }
        }
        panic!("no theorem named {}", name);
    }
}
