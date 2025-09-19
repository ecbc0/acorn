use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp, FunctionApplication};
use crate::atom::{Atom, AtomId, INVALID_SYNTHETIC_ID};
use crate::builder::BuildError;
use crate::clause::Clause;
use crate::fact::Fact;
use crate::goal::Goal;
use crate::literal::Literal;
use crate::monomorphizer::Monomorphizer;
use crate::names::ConstantName;
use crate::normalization_map::{NewConstantType, NormalizationMap};
use crate::proof_step::{ProofStep, Truthiness};
use crate::source::SourceType;
use crate::term::{Term, TypeId};

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

#[derive(Clone)]
pub struct Normalizer {
    monomorphizer: Monomorphizer,

    /// Types of the skolem functions produced
    /// Some of them are just constants, so we store an AcornType rather than a FunctionType
    skolem_types: Vec<AcornType>,

    /// skolem_info[id] contains the information about why this skolem function was created.
    skolem_info: Vec<Arc<SkolemInfo>>,

    /// Same information as `skolem_info`, but indexed by SkolemKey.
    /// This is used to avoid creating the same skolem function multiple times.
    skolem_map: HashMap<SkolemKey, Arc<SkolemInfo>>,

    normalization_map: NormalizationMap,
}

/// A normalized representation of an existential statement that we skolemized.
/// This lets us look up to see if we have skolemized an exact value before.
#[derive(Hash, Eq, PartialEq, Debug, Clone)]
struct SkolemKey {
    /// CNF form of the proposition that we skolemized.
    /// Here, the skolem constants have been turned into variables.
    /// This lets us to a lookup when we want to check if any skolem ids match.
    clauses: Vec<Clause>,

    /// The first `num_existential` variables in the clauses are existential.
    num_existential: usize,
}

impl std::fmt::Display for SkolemKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Join all the clauses with "and"
        let clauses_str: Vec<String> = self.clauses.iter().map(|c| c.to_string()).collect();
        let clauses = clauses_str.join(" and ");
        write!(
            f,
            "SkolemKey(num_existential: {}, clauses: {})",
            self.num_existential, clauses
        )
    }
}

impl SkolemKey {
    fn bucket(&self) -> (usize, usize) {
        (self.num_existential, self.clauses.len())
    }
}

/// Information about a particular skolem function that we created.
/// We will need to look this up both by skolem key, and by atom id.
pub struct SkolemInfo {
    /// CNF form of the proposition that we skolemized.
    /// Here, the skolem constants exist in the clauses.
    pub clauses: Vec<Clause>,

    /// Which skolem atoms were created in this skolemization.
    /// Each of these should be present in clauses.
    pub ids: Vec<AtomId>,
}

impl std::fmt::Display for SkolemInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Join all the clauses with "and"
        let clauses_str: Vec<String> = self.clauses.iter().map(|c| c.to_string()).collect();
        let clauses = clauses_str.join(" and ");
        write!(f, "SkolemInfo(ids: {:?}, clauses: {})", self.ids, clauses)
    }
}

impl Normalizer {
    pub fn new() -> Normalizer {
        Normalizer {
            monomorphizer: Monomorphizer::new(),
            skolem_types: vec![],
            skolem_info: vec![],
            skolem_map: HashMap::new(),
            normalization_map: NormalizationMap::new(),
        }
    }

    pub fn is_skolem(&self, atom: &Atom) -> bool {
        matches!(atom, Atom::Synthetic(_))
    }

    pub fn get_skolem_type(&self, id: AtomId) -> &AcornType {
        &self.skolem_types[id as usize]
    }

    /// Checks if there's an exact match for a skolem for the given value.
    /// The value should be of the form "exists ___ (forall x and forall y and ...)".
    pub fn has_exact_skolem_info(&mut self, value: &AcornValue) -> bool {
        // Remove exists quantifiers if present
        let (num_existential, after_exists) = match value {
            AcornValue::Exists(quants, subvalue) => (quants.len(), subvalue.as_ref().clone()),
            _ => (0, value.clone()),
        };

        let Ok(uninstantiated) = self.clauses_from_value(&after_exists) else {
            return false;
        };
        let clauses = uninstantiated
            .iter()
            .map(|c| c.instantiate_invalid_synthetics(num_existential))
            .collect();
        let key = SkolemKey {
            clauses,
            num_existential,
        };
        if self.skolem_map.contains_key(&key) {
            true
        } else {
            // Uncomment to debug lookups
            // self.debug_failed_lookup(&key);

            false
        }
    }

    // Useful for debugging
    #[allow(dead_code)]
    fn debug_failed_lookup(&self, key: &SkolemKey) {
        println!("Failed lookup for key: {}", key);

        for candidate in self.skolem_map.keys() {
            if candidate.bucket() == key.bucket() {
                println!("Candidate: {}", candidate);
            }
        }
    }

    /// The input should already have negations moved inwards.
    /// The stack must be entirely universal quantifiers.
    /// Outputs the new skolem atoms that were created.
    ///
    /// The value does *not* need to be in prenex normal form.
    /// I.e., it can still have quantifier nodes, either "exists" or "forall", inside of
    /// logical nodes, like "and" and "or".
    /// All negations must be moved inside quantifiers, though.
    ///
    /// In general I think converting to prenex seems bad. Consider:
    ///   forall(x, f(x)) & exists(y, g(y))
    /// If we convert to prenex, we get:
    ///   forall(x, exists(y, f(x) & g(y)))
    /// which skolemizes to
    ///   forall(x, f(x) & g(skolem(x)))
    /// But there's a redundant arg here. The simpler form is just
    ///   forall(x, f(x) & g(skolem()))
    /// which is what we get if we don't convert to prenex first.
    pub fn skolemize(
        &self,
        stack: &Vec<AcornType>,
        value: AcornValue,
        next_skolem_id: &mut AtomId,
        created: &mut Vec<(AtomId, AcornType)>,
    ) -> Result<AcornValue, String> {
        Ok(match value {
            AcornValue::ForAll(quants, subvalue) => {
                let mut new_stack = stack.clone();
                new_stack.extend(quants.clone());
                let new_subvalue =
                    self.skolemize(&new_stack, *subvalue, next_skolem_id, created)?;
                AcornValue::ForAll(quants, Box::new(new_subvalue))
            }

            AcornValue::Exists(quants, subvalue) => {
                // The current stack will be the arguments for the skolem functions
                let mut args = vec![];
                for (i, univ) in stack.iter().enumerate() {
                    args.push(AcornValue::Variable(i as AtomId, univ.clone()));
                }

                // Find a replacement for each of the quantifiers.
                // Each one will be a skolem function applied to the current stack.
                let mut replacements = vec![];
                for quant in quants {
                    // Make a new skolem atom
                    let skolem_type = AcornType::functional(stack.clone(), quant);
                    if *next_skolem_id >= INVALID_SYNTHETIC_ID {
                        return Err(format!("ran out of skolem ids (used {})", next_skolem_id));
                    }
                    let skolem_name = ConstantName::Synthetic(*next_skolem_id);
                    let skolem_value =
                        AcornValue::constant(skolem_name, vec![], skolem_type.clone());
                    created.push((*next_skolem_id, skolem_type));
                    *next_skolem_id += 1;
                    let replacement = AcornValue::apply(skolem_value, args.clone());
                    replacements.push(replacement);
                }

                // Replace references to the existential quantifiers
                let stack_size = stack.len() as AtomId;
                return self.skolemize(
                    stack,
                    subvalue.bind_values(stack_size, stack_size, &replacements),
                    next_skolem_id,
                    created,
                );
            }

            AcornValue::Binary(BinaryOp::And, left, right) => {
                let left = self.skolemize(stack, *left, next_skolem_id, created)?;
                let right = self.skolemize(stack, *right, next_skolem_id, created)?;
                AcornValue::Binary(BinaryOp::And, Box::new(left), Box::new(right))
            }

            AcornValue::Binary(BinaryOp::Or, left, right) => {
                let left = self.skolemize(stack, *left, next_skolem_id, created)?;
                let right = self.skolemize(stack, *right, next_skolem_id, created)?;
                AcornValue::Binary(BinaryOp::Or, Box::new(left), Box::new(right))
            }

            // Acceptable terminal nodes for the skolemization algorithm
            AcornValue::Application(_)
            | AcornValue::Not(_)
            | AcornValue::Binary(_, _, _)
            | AcornValue::Variable(_, _)
            | AcornValue::Bool(_)
            | AcornValue::Constant(_) => value,

            _ => {
                return Err(format!("failed to normalize value: {}", value));
            }
        })
    }

    /// Constructs a new term from a function application
    /// Function applications that are nested like f(x)(y) are flattened to f(x, y)
    fn term_from_application(
        &mut self,
        application: &FunctionApplication,
        ctype: NewConstantType,
    ) -> Result<Term, String> {
        let application_type = application.get_type();
        check_normalized_type(&application_type)?;
        let term_type = self.normalization_map.add_type(&application_type);
        let func_term = self.term_from_value(&application.function, ctype)?;
        let head = func_term.head;
        let head_type = func_term.head_type;
        let mut args = func_term.args;
        for arg in &application.args {
            args.push(self.term_from_value(arg, ctype)?);
        }
        Ok(Term::new(term_type, head_type, head, args))
    }

    /// Constructs a new term from an AcornValue
    /// Returns an error if it's inconvertible.
    /// The "ctype" parameter controls whether any newly discovered constants
    /// are local, global, or disallowed.
    pub fn term_from_value(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
    ) -> Result<Term, String> {
        let (t, negated) = self.maybe_negated_term_from_value(value, ctype)?;
        if negated {
            Err(format!(
                "Cannot convert {} to term because it is negated",
                value
            ))
        } else {
            Ok(t)
        }
    }

    fn atom_from_name(
        &mut self,
        name: &ConstantName,
        ctype: NewConstantType,
    ) -> Result<Atom, String> {
        if let ConstantName::Synthetic(i) = name {
            return Ok(Atom::Synthetic(*i));
        };

        if let Some(atom) = self.normalization_map.get_atom(name) {
            return Ok(atom);
        }

        // We have to create a new atom
        let local = match ctype {
            NewConstantType::Global => false,
            NewConstantType::Local => true,
            NewConstantType::Disallowed => return Err(format!("unrecognized name: {}", name)),
        };
        Ok(self.normalization_map.add_constant(name.clone(), local))
    }

    /// Constructs a new term or negated term from an AcornValue
    /// Returns an error if it's inconvertible.
    /// The "ctype" parameter controls whether any newly discovered constants
    /// are local, global, or disallowed.
    /// The flag returned is whether the term is negated.
    fn maybe_negated_term_from_value(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
    ) -> Result<(Term, bool), String> {
        match value {
            AcornValue::Variable(i, var_type) => {
                check_normalized_type(var_type)?;
                let type_id = self.normalization_map.add_type(var_type);
                Ok((
                    Term::new(type_id, type_id, Atom::Variable(*i), vec![]),
                    false,
                ))
            }
            AcornValue::Application(application) => {
                Ok((self.term_from_application(application, ctype)?, false))
            }
            AcornValue::Constant(c) => {
                if c.params.is_empty() {
                    check_normalized_type(&c.instance_type)?;
                    let type_id = self.normalization_map.add_type(&c.instance_type);
                    let constant_atom = self.atom_from_name(&c.name, ctype)?;
                    Ok((Term::new(type_id, type_id, constant_atom, vec![]), false))
                } else {
                    Ok((self.normalization_map.term_from_monomorph(&c), false))
                }
            }
            AcornValue::Bool(v) => Ok((Term::new_true(), !v)),
            AcornValue::Not(subvalue) => {
                let (term, negated) = self.maybe_negated_term_from_value(&*subvalue, ctype)?;
                Ok((term, !negated))
            }
            _ => Err(format!("Cannot convert {} to term", value)),
        }
    }

    /// Panics if this value cannot be converted to a literal.
    /// Swaps left and right if needed, to sort.
    /// Normalizes literals to <larger> = <smaller>, because that's the logical direction
    /// to do rewrite-type lookups, on the larger literal first.
    fn literal_from_value(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
    ) -> Result<Literal, String> {
        match value {
            AcornValue::Variable(_, _) | AcornValue::Constant(_) => {
                Ok(Literal::positive(self.term_from_value(value, ctype)?))
            }
            AcornValue::Application(app) => {
                Ok(Literal::positive(self.term_from_application(app, ctype)?))
            }
            AcornValue::Binary(BinaryOp::Equals, left, right) => {
                let (left_term, left_negated) =
                    self.maybe_negated_term_from_value(&*left, ctype)?;
                let (right_term, right_negated) =
                    self.maybe_negated_term_from_value(&*right, ctype)?;
                let negated = left_negated ^ right_negated;
                Ok(Literal::new(!negated, left_term, right_term))
            }
            AcornValue::Binary(BinaryOp::NotEquals, left, right) => {
                let (left_term, left_negated) =
                    self.maybe_negated_term_from_value(&*left, ctype)?;
                let (right_term, right_negated) =
                    self.maybe_negated_term_from_value(&*right, ctype)?;
                let negated = left_negated ^ right_negated;
                Ok(Literal::new(negated, left_term, right_term))
            }
            AcornValue::Not(subvalue) => {
                Ok(Literal::negative(self.term_from_value(subvalue, ctype)?))
            }
            _ => Err(format!("Cannot convert {} to literal", value)),
        }
    }

    /// Converts a value into a Vec<Literal> if possible.
    /// Ignores leading "forall" since the Clause leaves those implicit.
    /// Does not change variable ids or sort literals but does sort terms within literals.
    /// TODO: this shouldn't mutate self, but the helper functions do when called with
    /// different arguments, so the signature is mut.
    fn literals_from_value(&mut self, value: &AcornValue) -> Result<Vec<Literal>, String> {
        match value {
            AcornValue::ForAll(_, subvalue) => self.literals_from_value(subvalue),
            AcornValue::Binary(BinaryOp::Or, left_v, right_v) => {
                let mut lits = self.literals_from_value(left_v)?;
                let right_lits = self.literals_from_value(right_v)?;
                lits.extend(right_lits);
                Ok(lits)
            }
            _ => {
                let lit = self.literal_from_value(value, NewConstantType::Disallowed)?;
                Ok(vec![lit])
            }
        }
    }

    /// Does not change variable ids but does sort literals.
    pub fn clause_from_value(&mut self, value: &AcornValue) -> Result<Clause, String> {
        let mut literals = self.literals_from_value(value)?;
        literals.sort();
        Ok(Clause { literals })
    }

    /// Does not change variable ids but does sort literals.
    pub fn clauses_from_value(&mut self, value: &AcornValue) -> Result<Vec<Clause>, String> {
        if *value == AcornValue::Bool(true) {
            return Ok(vec![]);
        }
        let subvalues = value.remove_and();
        subvalues
            .into_iter()
            .map(|subvalue| self.clause_from_value(&subvalue))
            .collect()
    }

    pub fn add_local_constant(&mut self, cname: ConstantName) -> Atom {
        self.normalization_map.add_constant(cname, true)
    }

    /// Converts a value that is already in CNF into lists of literals.
    /// Each Vec<Literal> is a conjunction, an "or" node.
    /// The CNF form is expressing that each of these conjunctions are true.
    /// Returns Ok(Some(cnf)) if it can be turned into CNF.
    /// Returns Ok(None) if it's an impossibility.
    /// Returns an error if we failed in some user-reportable way.
    fn into_literal_lists(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
    ) -> Result<Option<Vec<Vec<Literal>>>, String> {
        match value {
            AcornValue::Binary(BinaryOp::And, left, right) => {
                let mut left = match self.into_literal_lists(left, ctype)? {
                    Some(left) => left,
                    None => return Ok(None),
                };
                let right = match self.into_literal_lists(right, ctype)? {
                    Some(right) => right,
                    None => return Ok(None),
                };
                left.extend(right);
                Ok(Some(left))
            }
            AcornValue::Binary(BinaryOp::Or, left, right) => {
                let left = self.into_literal_lists(left, ctype)?;
                let right = self.into_literal_lists(right, ctype)?;
                match (left, right) {
                    (None, None) => Ok(None),
                    (Some(result), None) | (None, Some(result)) => Ok(Some(result)),
                    (Some(left), Some(right)) => {
                        let mut results = vec![];
                        for left_result in &left {
                            for right_result in &right {
                                let mut combined = left_result.clone();
                                combined.extend(right_result.clone());
                                results.push(combined);
                            }
                        }
                        Ok(Some(results))
                    }
                }
            }
            AcornValue::Bool(true) => Ok(Some(vec![])),
            AcornValue::Bool(false) => Ok(None),
            _ => {
                let literal = self.literal_from_value(&value, ctype)?;
                if literal.is_tautology() {
                    Ok(Some(vec![]))
                } else {
                    Ok(Some(vec![vec![literal]]))
                }
            }
        }
    }

    /// Converts AcornValue to Vec<Clause> without changing the tree structure.
    /// The tree structure should already be manipulated before calling this.
    fn normalize_cnf(
        &mut self,
        value: AcornValue,
        ctype: NewConstantType,
    ) -> Result<Vec<Clause>, String> {
        let mut universal = vec![];
        let value = value.remove_forall(&mut universal);
        match self.into_literal_lists(&value, ctype) {
            Ok(Some(lists)) => Ok(self.normalize_literal_lists(lists)),
            Ok(None) => Ok(vec![Clause::impossible()]),
            Err(s) => {
                // value is essentially a subvalue with the universal quantifiers removed,
                // so reconstruct it to display it nicely.
                let reconstructed = AcornValue::forall(universal, value);
                Err(format!(
                    "\nerror converting {} to CNF:\n{}",
                    reconstructed, s
                ))
            }
        }
    }

    // Note that this can normalize the variable ids for each clause differently.
    // This is valid because clauses are separately universally quantified.
    fn normalize_literal_lists(&self, literal_lists: Vec<Vec<Literal>>) -> Vec<Clause> {
        let mut clauses = vec![];
        for literals in literal_lists {
            assert!(literals.len() > 0);
            let clause = Clause::new(literals);
            // println!("clause: {}", clause);
            clauses.push(clause);
        }
        clauses
    }

    /// Converts a value to CNF, then to Vec<Clause>.
    /// Does not handle the "definition" sorts of values.
    fn convert_then_normalize(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
    ) -> Result<Vec<Clause>, String> {
        // println!("\nnormalizing: {}", value);
        let value = value.replace_function_equality(0);
        let value = value.expand_lambdas(0);
        let value = value.replace_match();
        let value = value.replace_if();
        let value = value.move_negation_inwards(true, false);

        // println!("pre-skolemize: {}", value);
        let mut next_skolem_id = self.skolem_info.len() as AtomId;
        let mut created = vec![];
        let value = self.skolemize(&vec![], value, &mut next_skolem_id, &mut created)?;

        let clauses = self.normalize_cnf(value, ctype)?;

        if !created.is_empty() {
            let mut skolem_ids = vec![];
            for (skolem_id, skolem_type) in created {
                self.skolem_types.push(skolem_type);
                skolem_ids.push(skolem_id);
            }

            // In the skolem key, we normalize skolem ids by renumbering them.
            let skolem_key_form: Vec<_> = clauses
                .iter()
                .map(|c| c.invalidate_synthetics(&skolem_ids))
                .collect();
            let num_existential = skolem_ids.len();
            let key = SkolemKey {
                clauses: skolem_key_form.clone(),
                num_existential,
            };
            let info = Arc::new(SkolemInfo {
                clauses: clauses.clone(),
                ids: skolem_ids,
            });
            for _ in 0..num_existential {
                self.skolem_info.push(info.clone());
            }
            self.skolem_map.insert(key, info);
        }

        Ok(clauses)
    }

    /// Converts a value to CNF: Conjunctive Normal Form.
    /// In other words, a successfully normalized value turns into a bunch of clauses.
    /// Logically, this is an "and of ors".
    /// Each Clause represents an implicit "forall", plus an "or" of its literals.
    /// "true" is represented by an empty list, which is always satisfied.
    /// "false" is represented by a single impossible clause.
    pub fn normalize_value(
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
        assert_eq!(value.get_type(), AcornType::Bool);

        if let AcornValue::Binary(BinaryOp::Equals, left, right) = &value {
            // Check for the sort of functional equality that can be represented as a literal.
            if left.get_type().is_functional() && left.is_term() && right.is_term() {
                // We want to represent this two ways.
                // One as an equality between functions, another as an equality between
                // primitive types, after applying the functions.
                // If we handled functional types better in unification we might not need this.
                let mut functional = self.normalize_cnf(value.clone(), ctype)?;
                let mut primitive = self.convert_then_normalize(value, ctype)?;
                functional.append(&mut primitive);
                return Ok(functional);
            }
        }

        self.convert_then_normalize(value, ctype)
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
            let defined = match &proposition.source.source_type {
                SourceType::ConstantDefinition(value, _) => {
                    let term = self
                        .term_from_value(&value, ctype)
                        .map_err(|msg| BuildError::new(range, msg))?;
                    Some(term.get_head().clone())
                }
                _ => None,
            };
            let clauses = self
                .normalize_value(&proposition.value, ctype)
                .map_err(|msg| BuildError::new(range, msg))?;
            for clause in clauses {
                let step = ProofStep::assumption(&proposition, clause, defined);
                steps.push(step);
            }
        }
        Ok(steps)
    }

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
                let acorn_type = self.skolem_types[*i as usize].clone();
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
    /// The resulting value may have skolem atoms in it.
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

    /// Given a list of atom ids for skolems that we need to define, find a set
    /// of skolem information that covers them.
    /// The output may have skolems that aren't used in the input.
    /// The input doesn't have to be in order and may contain duplicates.
    pub fn find_covering_skolem_info(&self, ids: &[AtomId]) -> Vec<Arc<SkolemInfo>> {
        let mut covered = HashSet::new();
        let mut output = vec![];
        for id in ids {
            if covered.contains(id) {
                continue;
            }
            let info = self.skolem_info[*id as usize].clone();
            for skolem_id in &info.ids {
                covered.insert(*skolem_id);
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
        assert_eq!(clause, &renormalized[0]);
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

/// Returns an error if a type is not normalized.
fn check_normalized_type(acorn_type: &AcornType) -> Result<(), String> {
    match acorn_type {
        AcornType::Function(function_type) => {
            if function_type.arg_types.len() == 0 {
                return Err(format!("Function type {} has no arguments", function_type));
            }
            for arg_type in &function_type.arg_types {
                check_normalized_type(&arg_type)?;
            }
            if function_type.return_type.is_functional() {
                return Err(format!(
                    "Function type has a functional return type: {}",
                    function_type
                ));
            }
            check_normalized_type(&function_type.return_type)
        }
        AcornType::Bool => Ok(()),
        AcornType::Data(_, params) => {
            for param in params {
                check_normalized_type(&param)?;
            }
            Ok(())
        }
        AcornType::Variable(..) => {
            return Err(format!(
                "Type variables should be monomorphized before normalization: {}",
                acorn_type
            ));
        }
        AcornType::Empty => Ok(()),
        AcornType::Arbitrary(..) => Ok(()),
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
        assert_eq!(norm.skolem_types.len(), 1);
        assert_eq!(norm.skolem_info.len(), 1);
        assert_eq!(norm.skolem_map.len(), 1);
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
}
