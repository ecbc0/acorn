use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::{Atom, AtomId, INVALID_SYNTHETIC_ID};
use crate::builder::BuildError;
use crate::clause::Clause;
use crate::cnf::CNF;
use crate::fact::Fact;
use crate::goal::Goal;
use crate::literal::Literal;
use crate::monomorphizer::Monomorphizer;
use crate::names::ConstantName;
use crate::normalization_map::{NewConstantType, NormalizationMap};
use crate::proof_step::{ProofStep, Truthiness};
use crate::source::SourceType;
use crate::term::{Term, TypeId};

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

    /// The definition for each synthetic atom.
    synthetic_definitions: Vec<Arc<SyntheticDefinition>>,

    /// Same information as `synthetic_info`, but indexed by SyntheticKey.
    /// This is used to avoid defining the same thing multiple times.
    synthetic_map: HashMap<SyntheticKey, Arc<SyntheticDefinition>>,

    normalization_map: NormalizationMap,
}

impl Normalizer {
    pub fn new() -> Normalizer {
        Normalizer {
            monomorphizer: Monomorphizer::new(),
            synthetic_types: vec![],
            synthetic_definitions: vec![],
            synthetic_map: HashMap::new(),
            normalization_map: NormalizationMap::new(),
        }
    }

    pub fn get_synthetic_type(&self, id: AtomId) -> &AcornType {
        &self.synthetic_types[id as usize]
    }

    /// Checks if there's an exact match for a synthetic definition for the given value.
    /// The value should be of the form "exists ___ (forall x and forall y and ...)".
    /// This is a really wacky algorithm, it seems like we should clean it up.
    pub fn has_synthetic_definition(&mut self, value: &AcornValue) -> bool {
        let (num_definitions, alt_value) = match value {
            AcornValue::Exists(quants, subvalue) => (
                quants.len(),
                AcornValue::ForAll(quants.clone(), subvalue.clone()),
            ),
            _ => (0, value.clone()),
        };
        let mut view = NormalizerView::Ref(self);
        let Ok(uninstantiated) = view.value_to_denormalized_clauses(&alt_value) else {
            return false;
        };
        let clauses = uninstantiated
            .iter()
            .map(|c| c.instantiate_invalid_synthetics(num_definitions))
            .collect();
        let key = SyntheticKey {
            clauses,
            num_atoms: num_definitions,
        };
        self.synthetic_map.contains_key(&key)
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
        self.normalization_map.add_type(&atom_type);
        self.synthetic_types.push(atom_type);
        Ok(id)
    }

    /// Adds the definition for these synthetic atoms.
    /// This must be done in the same order they are declared in.
    fn define_synthetic_atoms(&mut self, atoms: Vec<AtomId>, clauses: Vec<Clause>) {
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
        });
        for atom in atoms {
            if atom as usize != self.synthetic_definitions.len() {
                panic!("synthetic atoms must be defined in order");
            }
            self.synthetic_definitions.push(info.clone());
        }
        self.synthetic_map.insert(key, info);
    }

    pub fn add_local_constant(&mut self, cname: ConstantName) -> Atom {
        self.normalization_map
            .add_constant(cname, NewConstantType::Local)
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
                let mut clauses = vec![];
                for literals in cnf.into_iter() {
                    if literals.iter().any(|l| l.is_tautology()) {
                        // This clause is always true, so skip it.
                        continue;
                    }
                    let clause = Clause::new(literals);
                    clauses.push(clause);
                }
                Ok(clauses)
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
        stack: &mut Vec<Term>,
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
                if let AcornValue::Lambda(_, return_value) = &*app.function {
                    let mut args = vec![];
                    for arg in &app.args {
                        args.push(self.value_to_term(arg, stack)?);
                    }
                    stack.extend(args);
                    let answer =
                        self.value_to_cnf(&return_value, negate, stack, next_var_id, synth);
                    stack.truncate(stack.len() - app.args.len());
                    return answer;
                }

                // Fall through
                self.value_to_single_term_to_cnf(value, negate, stack)
            }
            _ => self.value_to_single_term_to_cnf(value, negate, stack),
        }
    }

    // The "fallthrough" case for value_to_cnf.
    fn value_to_single_term_to_cnf(
        &mut self,
        value: &AcornValue,
        negate: bool,
        stack: &Vec<Term>,
    ) -> Result<CNF, String> {
        let (t, sign) = self.value_to_signed_term(value, stack)?;
        let literal = Literal::from_signed_term(t, sign ^ negate);
        Ok(CNF::from_literal(literal))
    }

    // Convert a "forall" node in a value, or the equivalent, to CNF.
    // negate is whether to negate the subvalue.
    fn forall_to_cnf(
        &mut self,
        quants: &Vec<AcornType>,
        subvalue: &AcornValue,
        negate: bool,
        stack: &mut Vec<Term>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<AtomId>,
    ) -> Result<CNF, String> {
        for quant in quants {
            let type_id = self.as_ref().normalization_map.get_type_id(quant)?;
            let var = Term::new_variable(type_id, *next_var_id);
            *next_var_id += 1;
            stack.push(var);
        }
        let result = self.value_to_cnf(subvalue, negate, stack, next_var_id, synthesized)?;
        for _ in quants {
            stack.pop();
        }
        Ok(result)
    }

    // Convert an "exists" node in a value, or the equivalent, to CNF.
    // negate is whether to negate the subvalue.
    fn exists_to_cnf(
        &mut self,
        quants: &Vec<AcornType>,
        subvalue: &AcornValue,
        negate: bool,
        stack: &mut Vec<Term>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<AtomId>,
    ) -> Result<CNF, String> {
        // The variables on the stack will be the arguments for the skolem functions
        let mut args = vec![];
        let mut arg_types = vec![];
        for term in stack.iter() {
            if term.is_variable() {
                args.push(term.clone());
                arg_types.push(
                    self.as_ref()
                        .normalization_map
                        .get_type(term.term_type)
                        .clone(),
                );
            }
        }
        for quant in quants {
            // Each existential quantifier needs a new skolem atom.
            // The skolem term is that atom applied to the variables on the stack.
            // Note that the skolem atom may be a type we have not used before.
            let skolem_atom_type = AcornType::functional(arg_types.clone(), quant.clone());
            let skolem_atom_type_id = self.as_mut()?.normalization_map.add_type(&skolem_atom_type);
            let skolem_term_type_id = self.as_ref().normalization_map.get_type_id(quant)?;
            let skolem_id = self.as_mut()?.declare_synthetic_atom(skolem_atom_type)?;
            synthesized.push(skolem_id);
            let skolem_atom = Atom::Synthetic(skolem_id);
            let skolem_term = Term::new(
                skolem_term_type_id,
                skolem_atom_type_id,
                skolem_atom,
                args.clone(),
            );
            stack.push(skolem_term);
        }
        let result = self.value_to_cnf(subvalue, negate, stack, next_var_id, synthesized)?;
        for _ in quants {
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
        stack: &mut Vec<Term>,
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
        stack: &mut Vec<Term>,
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
        stack: &mut Vec<Term>,
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

        if left.is_bool_type() {
            if let Some((left_term, left_sign)) = self.try_value_to_signed_term(left, stack)? {
                if let Some((right_term, right_sign)) =
                    self.try_value_to_signed_term(right, stack)?
                {
                    // Both sides are terms, so we can do a simple equality or inequality
                    let positive = (left_sign == right_sign) ^ negate;
                    let literal = Literal::new(positive, left_term, right_term);
                    return Ok(CNF::from_literal(literal));
                }
            }

            // This logic duplicates subterms. We need to be careful that we don't synthesize
            // variables in these calls.
            if negate {
                // Inequality.
                let some = self.or_to_cnf(left, right, true, true, stack, next_var_id, synth)?;
                let not_both =
                    self.or_to_cnf(left, right, false, false, stack, next_var_id, synth)?;
                Ok(some.and(not_both))
            } else {
                // Equality.
                let l_imp_r =
                    self.or_to_cnf(left, right, true, false, stack, next_var_id, synth)?;
                let r_imp_l =
                    self.or_to_cnf(left, right, false, true, stack, next_var_id, synth)?;
                Ok(l_imp_r.and(r_imp_l))
            }
        } else {
            let left = self.value_to_extended_term(left, stack, next_var_id, synth)?;
            let right = self.value_to_extended_term(right, stack, next_var_id, synth)?;
            match (left, right) {
                (ExtendedTerm::Signed(left, ls), ExtendedTerm::Signed(right, rs)) => {
                    let literal = Literal::new(!negate ^ !ls ^ !rs, left, right);
                    Ok(CNF::from_literal(literal))
                }
                (ExtendedTerm::If(cond, then_t, else_t), ExtendedTerm::Signed(right, rs)) => {
                    let then_lit = Literal::new(!negate ^ !rs, then_t, right.clone());
                    let else_lit = Literal::new(!negate ^ !rs, else_t, right);
                    Ok(CNF::literal_if(cond, then_lit, else_lit))
                }
                (ExtendedTerm::Signed(left, ls), ExtendedTerm::If(cond, then_t, else_t)) => {
                    let then_lit = Literal::new(!negate ^ !ls, left.clone(), then_t);
                    let else_lit = Literal::new(!negate ^ !ls, left, else_t);
                    Ok(CNF::literal_if(cond, then_lit, else_lit))
                }
                _ => Err("comparison between two 'if' values".to_string()),
            }
        }
    }

    fn value_to_term(&self, value: &AcornValue, stack: &Vec<Term>) -> Result<Term, String> {
        let (t, sign) = self.value_to_signed_term(value, stack)?;
        if sign {
            return Ok(t);
        }
        Err(format!("{} is unexpectedly negated", value))
    }

    /// Wrapper around try_value_to_signed_term that treats inconvertibility as an error.
    fn value_to_signed_term(
        &self,
        value: &AcornValue,
        stack: &Vec<Term>,
    ) -> Result<(Term, bool), String> {
        let answer = self.try_value_to_signed_term(value, stack)?;
        answer.ok_or_else(|| {
            // We might want to introduce a synthetic term here instead of giving up.
            format!("cannot convert {} to signed term", value)
        })
    }

    /// Helper for value_to_cnf.
    /// The bool returned is true = positive.
    /// This only errors if we get an inconsistent value.
    /// If it is just called on a value that doesn't convert to a term, it returns Ok(None).
    fn try_value_to_signed_term(
        &self,
        value: &AcornValue,
        stack: &Vec<Term>,
    ) -> Result<Option<(Term, bool)>, String> {
        match value {
            AcornValue::Variable(i, _) => {
                if (*i as usize) < stack.len() {
                    Ok(Some((stack[*i as usize].clone(), true)))
                } else {
                    Err(format!("variable {} out of range", i))
                }
            }
            AcornValue::Application(application) => {
                let application_type = application.get_type();
                let term_type = self
                    .as_ref()
                    .normalization_map
                    .get_type_id(&application_type)?;
                let func_term = self.value_to_term(&application.function, stack)?;
                let head = func_term.head;
                let head_type = func_term.head_type;
                let mut args = func_term.args;
                for arg in &application.args {
                    args.push(self.value_to_term(arg, stack)?);
                }
                Ok(Some((Term::new(term_type, head_type, head, args), true)))
            }
            AcornValue::Constant(c) => {
                if c.params.is_empty() {
                    let type_id = self
                        .as_ref()
                        .normalization_map
                        .get_type_id(&c.instance_type)?;

                    let Some(atom) = self.as_ref().normalization_map.get_atom(&c.name) else {
                        return Err(format!("constant {} not found in normalization map", c));
                    };
                    Ok(Some((Term::new(type_id, type_id, atom, vec![]), true)))
                } else {
                    Ok(Some((
                        self.as_ref().normalization_map.term_from_monomorph(&c)?,
                        true,
                    )))
                }
            }
            AcornValue::Not(subvalue) => match self.try_value_to_signed_term(subvalue, stack)? {
                None => Ok(None),
                Some((t, sign)) => Ok(Some((t, !sign))),
            },
            AcornValue::Bool(v) => Ok(Some((Term::new_true(), *v))),
            _ => Ok(None),
        }
    }

    /// Converts a value to an ExtendedTerm, which can appear in places a Term does.
    fn value_to_extended_term(
        &mut self,
        value: &AcornValue,
        stack: &mut Vec<Term>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<AtomId>,
    ) -> Result<ExtendedTerm, String> {
        match value {
            AcornValue::IfThenElse(cond_val, then_value, else_value) => {
                let cond_cnf = self.value_to_cnf(cond_val, false, stack, next_var_id, synth)?;
                let Some(cond_lit) = cond_cnf.to_literal() else {
                    return Err("term 'if' condition is too complicated".to_string());
                };
                let then_branch = self.value_to_term(then_value, stack)?;
                let else_branch = self.value_to_term(else_value, stack)?;
                Ok(ExtendedTerm::If(cond_lit, then_branch, else_branch))
            }
            AcornValue::Application(app) => {
                // We convert f(if a then b else c, d) into if a then f(b, d) else f(c, d).
                // The "spine" logic makes branching work for f as well.
                // If we discover a branching subterm, then we set cond and spine2.
                let mut cond: Option<Literal> = None;
                let mut spine1 = vec![];
                let mut spine2 = vec![];
                for subterm in app.iter_spine() {
                    match self.value_to_extended_term(subterm, stack, next_var_id, synth)? {
                        ExtendedTerm::Signed(t, sign) => {
                            if !sign {
                                return Err("negated term in application".to_string());
                            }
                            if !spine2.is_empty() {
                                spine2.push(t.clone());
                            }
                            spine1.push(t);
                        }
                        ExtendedTerm::If(sub_cond, sub_then, sub_else) => {
                            if !spine2.is_empty() {
                                return Err("multiple branches in application".to_string());
                            }
                            cond = Some(sub_cond);
                            spine2.extend(spine1.iter().cloned());
                            spine1.push(sub_then);
                            spine2.push(sub_else);
                        }
                    }
                }
                let term_type = self
                    .as_ref()
                    .normalization_map
                    .get_type_id(&app.get_type())?;
                match cond {
                    Some(cond) => {
                        assert_eq!(spine1.len(), spine2.len());
                        let then_term = Term::from_spine(spine1, term_type);
                        let else_term = Term::from_spine(spine2, term_type);
                        Ok(ExtendedTerm::If(cond, then_term, else_term))
                    }
                    None => {
                        assert!(spine2.is_empty());
                        let term = Term::from_spine(spine1, term_type);
                        Ok(ExtendedTerm::Signed(term, true))
                    }
                }
            }
            _ => {
                let term = self.value_to_term(value, stack)?;
                Ok(ExtendedTerm::Signed(term, true))
            }
        }
    }
}

// An ExtendedTerm can be a term but also a negated term or an if-then-else construct.
enum ExtendedTerm {
    // true = positive.
    Signed(Term, bool),

    // (condition, then branch, else branch)
    If(Literal, Term, Term),
}

impl Normalizer {
    /// This should handle any sort of boolean value.
    /// TODO: port edge cases into the "nice" value to clauses so that we only have one of these.
    fn ugly_value_to_clauses(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
    ) -> Result<Vec<Clause>, String> {
        self.normalization_map.add_from(&value, ctype);

        let value = value.replace_function_equality(0);

        // TODO: remove this line
        let value = value.expand_lambdas(0);

        let mut skolem_ids = vec![];
        let mut mut_view = NormalizerView::Mut(self);
        let clauses = mut_view.nice_value_to_clauses(&value, &mut skolem_ids)?;

        if !skolem_ids.is_empty() {
            // We have to define the skolem atoms that were declared during skolemization.
            self.define_synthetic_atoms(skolem_ids, clauses.clone());
        }

        // We should have defined all the synthetic atoms we declared at this point.
        assert!(self.synthetic_definitions.len() == self.synthetic_types.len());

        Ok(clauses)
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
    ) -> Result<Vec<Clause>, String> {
        if let Err(e) = value.validate() {
            return Err(format!(
                "validation error: {} while normalizing: {}",
                e, value
            ));
        }
        assert!(value.is_bool_type());

        let mut clauses = self.ugly_value_to_clauses(value, ctype)?;

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
                let left_term = view.value_to_term(left, &mut vec![])?;
                let right_term = view.value_to_term(right, &mut vec![])?;
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
            self.normalization_map
                .alias_monomorph(ci, name, &constant_type, local);
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
                .normalize_value(&proposition.value, ctype)
                .map_err(|msg| BuildError::new(range, msg))?;
            let defined = match &proposition.source.source_type {
                SourceType::ConstantDefinition(value, _) => {
                    let view = NormalizerView::Ref(self);
                    let term = view.value_to_term(value, &mut vec![]).map_err(|msg| {
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
        var_types: &mut Vec<AcornType>,
        arbitrary_names: Option<&HashMap<TypeId, ConstantName>>,
    ) -> AcornValue {
        let acorn_type = self.normalization_map.get_type(atom_type).clone();
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
                let index = *i as usize;
                if index < var_types.len() {
                    assert_eq!(var_types[index], acorn_type);
                } else if index == var_types.len() {
                    var_types.push(acorn_type.clone());
                } else {
                    panic!("variable index out of order");
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
        var_types: &mut Vec<AcornType>,
        arbitrary_names: Option<&HashMap<TypeId, ConstantName>>,
    ) -> AcornValue {
        let head = self.denormalize_atom(term.head_type, &term.head, var_types, arbitrary_names);
        let args: Vec<_> = term
            .args
            .iter()
            .map(|t| self.denormalize_term(t, var_types, arbitrary_names))
            .collect();
        AcornValue::apply(head, args)
    }

    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// Any other free variables are left unbound. Their types are accumulated.
    fn denormalize_literal(
        &self,
        literal: &Literal,
        var_types: &mut Vec<AcornType>,
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
        let mut var_types = vec![];
        let mut denormalized_literals = vec![];
        for literal in &clause.literals {
            denormalized_literals.push(self.denormalize_literal(
                literal,
                &mut var_types,
                arbitrary_names,
            ));
        }
        let disjunction = AcornValue::reduce(BinaryOp::Or, denormalized_literals);
        AcornValue::forall(var_types, disjunction)
    }

    pub fn denormalize_type(&self, type_id: TypeId) -> AcornType {
        self.normalization_map.get_type(type_id).clone()
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
            let info = self.synthetic_definitions[*id as usize].clone();
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
            .normalize_value(&denormalized, NewConstantType::Local)
            .unwrap();
        if renormalized.len() != 1 {
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

        let actual = self.normalize_value(value, NewConstantType::Local).unwrap();
        if actual.len() != expected.len() {
            panic!(
                "expected {} clauses, got {}:\n{}",
                expected.len(),
                actual.len(),
                actual
                    .iter()
                    .map(|c| format!("{}", c))
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

#[cfg(test)]
mod tests {
    use crate::environment::Environment;

    use super::*;

    #[test]
    fn test_nat_normalization() {
        let mut env = Environment::test();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("let zero: Nat = axiom");
        env.expect_type("zero", "Nat");
        env.add("let suc: Nat -> Nat = axiom");
        env.expect_type("suc", "Nat -> Nat");
        env.add("let one: Nat = suc(zero)");
        env.expect_type("one", "Nat");

        env.add("axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) implies x = y }");
        norm.check(&env, "suc_injective", &["suc(x0) != suc(x1) or x0 = x1"]);
        env.expect_type("suc_injective", "(Nat, Nat) -> Bool");

        env.add("axiom suc_neq_zero(x: Nat) { suc(x) != zero }");
        norm.check(&env, "suc_neq_zero", &["zero != suc(x0)"]);
        env.expect_type("suc_neq_zero", "Nat -> Bool");

        env.add(
            "axiom induction(f: Nat -> Bool) {\
            f(zero) and forall(k: Nat) { f(k) implies f(suc(k)) } implies forall(n: Nat) { f(n) } }",
        );

        norm.check(
            &env,
            "induction",
            &[
                "not x0(zero) or x0(s0(x0)) or x0(x1)",
                "not x0(suc(s0(x0))) or not x0(zero) or x0(x1)",
            ],
        );

        env.expect_type("induction", "(Nat -> Bool) -> Bool");

        env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }");
        env.expect_type("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

        env.add("axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }");
        env.expect_type("recursion_base", "(Nat -> Nat, Nat) -> Bool");
        norm.check(&env, "recursion_base", &["recursion(x0, x1, zero) = x1"]);

        env.add(
            "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat) {\
            recursion(f, a, suc(n)) = f(recursion(f, a, n)) }",
        );
        env.expect_type("recursion_step", "(Nat -> Nat, Nat, Nat) -> Bool");
        norm.check(
            &env,
            "recursion_step",
            &["recursion(x0, x1, suc(x2)) = x0(recursion(x0, x1, x2))"],
        );
    }

    #[test]
    fn test_bool_formulas() {
        let mut env = Environment::test();
        let mut norm = Normalizer::new();
        env.add("theorem one(a: Bool) { a implies a or (a or a) }");
        norm.check(&env, "one", &["not x0 or x0"]);

        env.add("theorem two(a: Bool) { a implies a and (a and a) }");
        norm.check(
            &env,
            "two",
            &["not x0 or x0", "not x0 or x0", "not x0 or x0"],
        );
    }

    #[test]
    fn test_tautology_elimination() {
        let mut env = Environment::test();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("theorem one(n: Nat) { n = n }");
        norm.check(&env, "one", &[]);

        env.add("theorem two(n: Nat) { n = n or n != n }");
        norm.check(&env, "two", &[]);
    }

    #[test]
    fn test_nested_skolemization() {
        let mut env = Environment::test();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("theorem exists_eq(x: Nat) { exists(y: Nat) { x = y } }");
        norm.check(&env, "exists_eq", &["s0(x0) = x0"]);
    }

    #[test]
    fn test_second_order_binding() {
        let mut env = Environment::test();
        env.add(
            r#"
            type Nat: axiom
            let borf: (Nat, Nat, Nat) -> Bool = axiom
            define also_borf(a: Nat, b: Nat, c: Nat) -> Bool { borf(a, b, c) }
            let bb: Nat = axiom
            let cc: Nat = axiom
            define specific_borf(x: Nat) -> Bool { also_borf(x, bb, cc) }
            define always_true(f: Nat -> Bool) -> Bool { forall(n: Nat) { f(n) } }
            theorem goal { not always_true(specific_borf) }
        "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["not always_true(specific_borf)"]);
    }

    #[test]
    fn test_boolean_equality() {
        let mut env = Environment::test();
        env.add(
            r#"
            type Nat: axiom
            let n0: Nat = axiom
            let n1: Nat = axiom
            let n2: Nat = axiom
            let n3: Nat = axiom
            theorem goal { (n0 = n1) = (n2 = n3) }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(
            &env,
            "goal",
            &["n1 != n0 or n3 = n2", "n3 != n2 or n1 = n0"],
        );
    }

    #[test]
    fn test_boolean_inequality() {
        let mut env = Environment::test();
        env.add(
            r#"
            type Nat: axiom
            let n0: Nat = axiom
            let n1: Nat = axiom
            let n2: Nat = axiom
            let n3: Nat = axiom
            theorem goal { (n0 = n1) != (n2 = n3) }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(
            &env,
            "goal",
            &["n3 != n2 or n1 != n0", "n3 = n2 or n1 = n0"],
        );
    }

    #[test]
    fn test_functions_returning_lambdas() {
        let mut env = Environment::test();
        env.add(
            r#"
            type Nat: axiom
            let addx: (Nat, Nat) -> Nat = axiom
            define adder(a: Nat) -> (Nat -> Nat) { function(b: Nat) { addx(a, b) } }
            theorem goal(a: Nat, b: Nat) { adder(a)(b) = adder(b)(a) }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["adder(x0, x1) = adder(x1, x0)"]);
    }

    #[test]
    fn test_functional_equality() {
        let mut env = Environment::test();
        env.add(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            define zerof(a: Nat) -> (Nat -> Nat) { function(b: Nat) { zero } }
            theorem goal(a: Nat, b: Nat) { zerof(a) = zerof(b) }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["zerof(x0, x1) = zerof(x2, x1)"]);
    }

    #[test]
    fn test_normalizing_exists() {
        let mut env = Environment::test();
        env.add(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            theorem goal { exists(x: Nat) { addx(x, zero) = one } }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["addx(s0, zero) = one"]);
        assert_eq!(norm.synthetic_types.len(), 1);
        assert_eq!(norm.synthetic_definitions.len(), 1);
        assert_eq!(norm.synthetic_map.len(), 1);
    }

    #[test]
    fn test_denormalizing_disjunction() {
        let mut env = Environment::test();
        env.add(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            let ltx: (Nat, Nat) -> Bool = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            theorem foo(x0: Nat, x1: Nat) { addx(addx(x0, zero), x1) != zero or ltx(x1, zero) }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(
            &env,
            "foo",
            &["addx(addx(x0, zero), x1) != zero or ltx(x1, zero)"],
        );
    }

    #[test]
    fn test_functional_skolemization() {
        // This matches a pattern that failed in finite_constraint proving
        let mut env = Environment::test();
        env.add(
            r#"
            type T: axiom
            type List: axiom
            let contains: (List, T) -> Bool = axiom
            define finite_constraint(p: T -> Bool) -> Bool {
                exists(lst: List) {
                    forall(x: T) {
                        p(x) implies contains(lst, x)
                    }
                }
            }
            theorem test_finite(p: T -> Bool) {
                not finite_constraint(p) or
                exists(lst: List) {
                    forall(x: T) {
                        p(x) implies contains(lst, x)
                    }
                }
            }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(
            &env,
            "test_finite",
            &["not finite_constraint(x0) or not x0(x1) or contains(s0(x0), x1)"],
        );
    }

    #[test]
    fn test_if_then_else_under_equality() {
        let mut env = Environment::test();
        env.add(
            r#"
            let a: Bool = axiom
            let b: Bool = axiom
            let c: Bool = axiom
            let d: Bool = axiom

            theorem goal {
                a = if b {
                    c
                } else {
                    d
                }
            }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(
            &env,
            "goal",
            &[
                "not b or not a or c",
                "not a or d or b",
                "not c or not b or a",
                "not d or b or a",
            ],
        );
    }

    #[test]
    fn test_if_then_else_with_true_branch_under_equality() {
        let mut env = Environment::test();
        env.add(
            r#"
            let a: Bool = axiom
            let b: Bool = axiom
            let d: Bool = axiom

            theorem goal {
                a = if b {
                    true
                } else {
                    d
                }
            }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(
            &env,
            "goal",
            &["not a or d or b", "not b or a", "not d or b or a"],
        );
    }

    #[test]
    fn test_if_then_else_normalization_with_variables() {
        let mut env = Environment::test();
        env.add(
            r#"
            type T: axiom
            let foo: (T -> Bool, T, T) -> Bool = axiom

            theorem goal(f: T -> Bool, item: T, x: T) {
                foo(f, item, x) = if x = item {
                    true
                } else {
                    f(x)
                }
            }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(
            &env,
            "goal",
            &[
                "not foo(x0, x1, x2) or x1 = x2 or x0(x2)",
                "x0 != x1 or foo(x2, x0, x1)",
                "not x0(x1) or foo(x0, x2, x1) or x1 = x2",
            ],
        );
    }

    #[test]
    fn test_lambda_normalization() {
        let mut env = Environment::test();
        env.add(
            r#"
            type Nat: axiom
            
            let f1: (Nat, Nat) -> Nat = axiom
            let f2: (Nat, Nat) -> Nat = axiom

            theorem goal {
                forall(a: Nat) {
                    f1(a) = function(b: Nat) {
                        f2(a)(b)
                    }
                }
            }
        "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["f2(x0, x1) = f1(x0, x1)"]);
    }
}
