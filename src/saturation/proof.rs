use std::collections::{HashMap, HashSet};

use crate::certificate::Certificate;
use crate::code_generator::{CodeGenerator, Error};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::kernel::fat_clause::FatClause;
use crate::kernel::fat_literal::FatLiteral;
use crate::kernel::local_context::LocalContext;
use crate::kernel::trace::LiteralTrace;
use crate::kernel::unifier::{Scope, Unifier};
use crate::kernel::variable_map::VariableMap;
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, ProofStepId, Rule};

/// A proof that was successfully found by the prover.
///
/// This is the internal form of the proof. The exportable form is a Certificate,
/// which can always be created and is fast to check.
///
/// We store each step of the proof in the order we found them, in `steps`.
/// This represents a proof by contradiction, with each step depending only on
/// previous steps.
pub struct Proof<'a> {
    normalizer: &'a Normalizer,

    // Steps of the proof that can be directly verified.
    // Represents a proof by contradiction, with each step depending only on
    // previous steps.
    pub steps: Vec<(ProofStepId, &'a ProofStep)>,

    // Same data as steps, but indexed.
    step_map: HashMap<ProofStepId, &'a ProofStep>,
}

impl<'a> Proof<'a> {
    /// Creates a new proof.
    pub fn new<'b>(normalizer: &'a Normalizer, _negated_goal: &AcornValue) -> Proof<'a> {
        Proof {
            normalizer,
            steps: vec![],
            step_map: HashMap::new(),
        }
    }

    /// Add a new step to the proof.
    pub fn add_step(&mut self, id: ProofStepId, step: &'a ProofStep) {
        self.step_map.insert(id.clone(), step);
        self.steps.push((id, step));
    }

    fn get_clause(&self, id: ProofStepId) -> Result<&FatClause, Error> {
        let step = self.step_map.get(&id).ok_or_else(|| {
            Error::internal(format!(
                "no node found for proof step {:?} in proof graph",
                id
            ))
        })?;
        Ok(&step.clause)
    }
}

// Each step in the ConcreteProof is associated with a ConcreteStepId.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ConcreteStepId {
    // This concrete step matches the *output* of a proof step.
    ProofStep(ProofStepId),

    // This concrete step matches the *input* of an assumption.
    // The assumption is a proof step, but its output is simplified, and this represents
    // the original assumption.
    Assumption(ProofStepId),
}

// In the order that they are logically deduced, because the assumption comes first.
fn concrete_ids_for(ps_id: ProofStepId) -> [ConcreteStepId; 2] {
    let assumption_id = ConcreteStepId::Assumption(ps_id);
    let concrete_id = ConcreteStepId::ProofStep(ps_id);
    [assumption_id, concrete_id]
}

// A concrete version of the proof step that has been reconstructed from the proof.
pub struct ConcreteStep {
    // The generic clause for this proof step.
    pub generic: FatClause,

    // All of the ways to map the generic variables to concrete ones.
    pub var_maps: HashSet<VariableMap>,
}

impl ConcreteStep {
    fn new(generic: FatClause, var_map: VariableMap) -> Self {
        ConcreteStep {
            generic,
            var_maps: HashSet::from([var_map]),
        }
    }
}

impl<'a> Proof<'a> {
    /// Create a certificate for this proof.
    pub fn make_cert(&self, goal: String, bindings: &BindingMap) -> Result<Certificate, Error> {
        let mut generator = CodeGenerator::new(&bindings);

        // First, reconstruct all the steps, working backwards.
        let mut concrete_steps: HashMap<ConcreteStepId, ConcreteStep> = HashMap::new();
        for (id, step) in self.steps.iter().rev() {
            if *id == ProofStepId::Final {
                self.reconstruct_step(*id, step, VariableMap::new(), &mut concrete_steps)?;
                continue;
            }
            // Multiple concrete instantiations are possible
            let concrete_id = ConcreteStepId::ProofStep(id.clone());
            let var_maps: Vec<_> = match concrete_steps.get(&concrete_id) {
                Some(concrete_step) => concrete_step.var_maps.iter().cloned().collect(),
                None => continue,
            };
            for var_map in var_maps {
                self.reconstruct_step(*id, step, var_map, &mut concrete_steps)?;
            }
        }

        // Skip the code that comes from concrete assumptions, because we don't need it
        // TODO: should we actually be skipping the original assumptions rather than
        // the simplified versions?
        let mut skip_code = HashSet::new();
        let mut synthetic_definitions = Vec::new();
        for (ps_id, step) in &self.steps {
            let concrete_id = ConcreteStepId::ProofStep(*ps_id);
            if step.rule.is_assumption() && !step.clause.has_any_variable() {
                let Some(cs) = concrete_steps.remove(&concrete_id) else {
                    continue;
                };
                let (definitions, codes) = generator.concrete_step_to_code(&cs, self.normalizer)?;
                // Collect all synthetic atom definitions
                for def in definitions {
                    if !synthetic_definitions.contains(&def) {
                        synthetic_definitions.push(def);
                    }
                }
                // Skip the actual clause codes from concrete assumptions
                for code in codes {
                    skip_code.insert(code);
                }
            }
        }

        // Start with synthetic atom definitions
        let mut answer = synthetic_definitions;
        for (ps_id, _) in &self.steps {
            for concrete_id in concrete_ids_for(*ps_id) {
                let Some(cs) = concrete_steps.remove(&concrete_id) else {
                    continue;
                };
                let (definitions, codes) = generator.concrete_step_to_code(&cs, self.normalizer)?;
                // Add any new definitions
                for def in definitions {
                    if !answer.contains(&def) {
                        answer.push(def);
                    }
                }
                // Add the clause codes if not skipped
                for code in codes {
                    if !answer.contains(&code) && !skip_code.contains(&code) {
                        answer.push(code);
                    }
                }
            }
        }
        Ok(Certificate::new(goal, answer))
    }

    // Adds a var map for a non-assumption proof step.
    fn add_var_map(
        &self,
        id: ProofStepId,
        var_map: VariableMap,
        concrete_steps: &mut HashMap<ConcreteStepId, ConcreteStep>,
    ) {
        let generic = self.get_clause(id).unwrap();
        match concrete_steps.entry(ConcreteStepId::ProofStep(id)) {
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                let concrete_step = entry.get_mut();
                concrete_step.var_maps.insert(var_map);
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                let concrete_step = ConcreteStep::new(generic.clone(), var_map);
                entry.insert(concrete_step);
            }
        }
    }

    // Given a varmap for the conclusion of a proof step, reconstruct varmaps for
    // all of its inputs.
    // The varmaps represent a concrete clause, in the sense that they provide a mapping to specialize
    // the clause into something concrete.
    //
    // Reconstructed varmaps are added to concrete_steps.
    // If the step cannot be reconstructed, we return an error.
    fn reconstruct_step(
        &self,
        id: ProofStepId,
        step: &ProofStep,
        conclusion_map: VariableMap,
        concrete_steps: &mut HashMap<ConcreteStepId, ConcreteStep>,
    ) -> Result<(), Error> {
        // Some rules we can handle without the traces.
        match &step.rule {
            Rule::PassiveContradiction(_) | Rule::MultipleRewrite(_) => {
                // These rules always use concrete premises, so we can track them without
                // reconstruction logic.
                for id in step.rule.premises() {
                    let map = VariableMap::new();
                    self.add_var_map(id, map, concrete_steps);
                }
                return Ok(());
            }
            _ => {}
        }

        let Some(traces) = step.trace.as_ref() else {
            return Err(Error::internal(format!(
                "no trace for {}: {}",
                step.rule.name(),
                &step.clause
            )));
        };

        match &step.rule {
            Rule::Assumption(info) => {
                // We need to reconstruct assumptions because assumptions can be simplified in
                // a way that we need to reconstruct.
                let var_maps = self.reconstruct_trace(
                    &info.literals,
                    traces.as_slice(),
                    &step.clause,
                    conclusion_map,
                    concrete_steps,
                )?;
                let assumption_id = ConcreteStepId::Assumption(id);
                for var_map in var_maps {
                    if var_map.len() == 0 {
                        // We don't need to track exact concrete assumptions.
                        continue;
                    }
                    match concrete_steps.entry(assumption_id) {
                        std::collections::hash_map::Entry::Occupied(mut entry) => {
                            let concrete_step = entry.get_mut();
                            concrete_step.var_maps.insert(var_map);
                        }
                        std::collections::hash_map::Entry::Vacant(entry) => {
                            let generic = FatClause::new_without_context(info.literals.clone());
                            let concrete_step = ConcreteStep::new(generic, var_map);
                            entry.insert(concrete_step);
                        }
                    }
                }
            }
            Rule::Rewrite(info) => {
                // For rewrites, the trace applies to the rewritten clause.
                let literals = vec![info.rewritten.clone()];
                let var_maps = self.reconstruct_trace(
                    &literals,
                    traces.as_slice(),
                    &step.clause,
                    conclusion_map,
                    concrete_steps,
                )?;

                // The target is already concrete, and the conclusion has been made concrete through
                // its variable map. We need to unify the pattern.
                let pattern_id = ProofStepId::Active(info.pattern_id);
                let pattern_clause = &self.get_clause(pattern_id)?;
                let pattern = &pattern_clause.literals[0];
                let target_id = ProofStepId::Active(info.target_id);
                let target_clause = &self.get_clause(target_id)?;
                let target = &target_clause.literals[0];
                let (from_pat, to_pat) = if info.forwards {
                    (&pattern.left, &pattern.right)
                } else {
                    (&pattern.right, &pattern.left)
                };
                let target_term = if info.target_left {
                    &target.left
                } else {
                    &target.right
                };
                let target_subterm = target_term.get_term_at_path(&info.path).unwrap();
                let rewritten_term = if info.target_left ^ info.flipped {
                    &info.rewritten.left
                } else {
                    &info.rewritten.right
                };
                let rewritten_subterm = rewritten_term.get_term_at_path(&info.path).unwrap();
                for conc_map in var_maps {
                    let (mut unifier, conc_scope) =
                        Unifier::with_map(conc_map, self.normalizer.kernel_context());
                    unifier.set_input_context(conc_scope, LocalContext::empty_ref());
                    let pattern_scope = unifier.add_scope();
                    unifier.set_input_context(pattern_scope, LocalContext::empty_ref());
                    assert!(unifier.unify(pattern_scope, from_pat, conc_scope, target_subterm));
                    assert!(unifier.unify(pattern_scope, to_pat, conc_scope, rewritten_subterm));

                    // Report the concrete pattern
                    let map = unifier.into_one_map(pattern_scope);
                    self.add_var_map(pattern_id, map, concrete_steps);
                }

                // The target is already concrete
                let map = VariableMap::new();
                self.add_var_map(target_id, map, concrete_steps);
            }
            Rule::EqualityFactoring(info) => {
                // For EF, the trace applies to the stored literals.
                let var_maps = self.reconstruct_trace(
                    &info.literals,
                    traces.as_slice(),
                    &step.clause,
                    conclusion_map,
                    concrete_steps,
                )?;

                // Unify the pre-EF and post-EF literals.
                let base_id = ProofStepId::Active(info.id);
                let base_clause = &self.get_clause(base_id)?;
                assert!(base_clause.literals.len() == info.literals.len());

                for conc_map in var_maps {
                    let (mut unifier, conc_scope) =
                        Unifier::with_map(conc_map, self.normalizer.kernel_context());
                    unifier.set_input_context(conc_scope, LocalContext::empty_ref());
                    let base_scope = unifier.add_scope();
                    unifier.set_input_context(base_scope, base_clause.get_local_context());

                    for (base_lit, lit_trace) in base_clause.literals.iter().zip(&info.ef_trace) {
                        for (base_term, term_trace) in [
                            (&base_lit.left, &lit_trace.left),
                            (&base_lit.right, &lit_trace.right),
                        ] {
                            let out_lit = &info.literals[term_trace.index];
                            let out_term = if term_trace.left {
                                &out_lit.left
                            } else {
                                &out_lit.right
                            };
                            assert!(unifier.unify(base_scope, base_term, conc_scope, out_term));
                        }
                    }

                    // Report the concrete base
                    let map = unifier.into_one_map(base_scope);
                    self.add_var_map(base_id, map, concrete_steps);
                }
            }
            Rule::EqualityResolution(info) => {
                // For ER, the trace applies to the stored literals.
                let var_maps = self.reconstruct_trace(
                    &info.literals,
                    traces.as_slice(),
                    &step.clause,
                    conclusion_map,
                    concrete_steps,
                )?;

                // Unify the pre-ER and post-ER literals.
                let base_id = ProofStepId::Active(info.id);
                let base_clause = &self.get_clause(base_id)?;
                assert!(base_clause.literals.len() == info.literals.len() + 1);

                for conc_map in var_maps {
                    let (mut unifier, conc_scope) =
                        Unifier::with_map(conc_map, self.normalizer.kernel_context());
                    unifier.set_input_context(conc_scope, LocalContext::empty_ref());
                    let base_scope = unifier.add_scope();
                    unifier.set_input_context(base_scope, base_clause.get_local_context());
                    let mut j = 0;
                    for (i, base_lit) in base_clause.literals.iter().enumerate() {
                        if i == info.index {
                            assert!(!base_lit.positive);
                            assert!(unifier.unify(
                                base_scope,
                                &base_lit.left,
                                base_scope,
                                &base_lit.right
                            ));
                            continue;
                        }
                        let (left, right) = if info.flipped[j] {
                            (&info.literals[j].right, &info.literals[j].left)
                        } else {
                            (&info.literals[j].left, &info.literals[j].right)
                        };

                        assert!(unifier.unify(base_scope, &base_lit.left, conc_scope, left));
                        assert!(unifier.unify(base_scope, &base_lit.right, conc_scope, right));
                        j += 1;
                    }

                    // Report the concrete base
                    let map = unifier.into_one_map(base_scope);
                    self.add_var_map(base_id, map, concrete_steps);
                }
            }
            Rule::Injectivity(info) => {
                // For injectivity, the trace applies to the stored literals.
                let var_maps = self.reconstruct_trace(
                    &info.literals,
                    traces.as_slice(),
                    &step.clause,
                    conclusion_map,
                    concrete_steps,
                )?;

                // Unify the pre-injectivity and post-injectivity literals.
                let base_id = ProofStepId::Active(info.id);
                let base_clause = &self.get_clause(base_id)?;
                assert!(base_clause.literals.len() == info.literals.len());

                for conc_map in var_maps {
                    let (mut unifier, conc_scope) =
                        Unifier::with_map(conc_map, self.normalizer.kernel_context());
                    unifier.set_input_context(conc_scope, LocalContext::empty_ref());
                    let base_scope = unifier.add_scope();
                    unifier.set_input_context(base_scope, base_clause.get_local_context());

                    for (i, (base_lit, info_lit)) in
                        base_clause.literals.iter().zip(&info.literals).enumerate()
                    {
                        if i == info.index {
                            let base_left = &base_lit.left.args()[info.arg];
                            let base_right = &base_lit.right.args()[info.arg];
                            let (left, right) = if info.flipped {
                                (&info_lit.right, &info_lit.left)
                            } else {
                                (&info_lit.left, &info_lit.right)
                            };
                            assert!(unifier.unify(base_scope, base_left, conc_scope, left));
                            assert!(unifier.unify(base_scope, base_right, conc_scope, right));
                        } else {
                            assert!(unifier.unify(
                                base_scope,
                                &base_lit.left,
                                conc_scope,
                                &info_lit.left
                            ));
                            assert!(unifier.unify(
                                base_scope,
                                &base_lit.right,
                                conc_scope,
                                &info_lit.right
                            ));
                        }
                    }

                    // Report the concrete base
                    let map = unifier.into_one_map(base_scope);
                    self.add_var_map(base_id, map, concrete_steps);
                }
            }
            Rule::BooleanReduction(info) => {
                // For boolean reduction, the trace applies to the stored literals.
                let var_maps = self.reconstruct_trace(
                    &info.literals,
                    traces.as_slice(),
                    &step.clause,
                    conclusion_map,
                    concrete_steps,
                )?;

                // Unify the pre-reduction and post-reduction literals.
                let base_id = ProofStepId::Active(info.id);
                let base_clause = &self.get_clause(base_id)?;
                assert!(base_clause.literals.len() + 1 == info.literals.len());

                for conc_map in var_maps {
                    let (mut unifier, conc_scope) =
                        Unifier::with_map(conc_map, self.normalizer.kernel_context());
                    unifier.set_input_context(conc_scope, LocalContext::empty_ref());
                    let base_scope = unifier.add_scope();
                    unifier.set_input_context(base_scope, base_clause.get_local_context());

                    for i in 0..info.index {
                        let base = &base_clause.literals[i];
                        let red = &info.literals[i];
                        assert!(unifier.unify(base_scope, &base.left, conc_scope, &red.left));
                        assert!(unifier.unify(base_scope, &base.right, conc_scope, &red.right));
                    }

                    let base = &base_clause.literals[info.index];
                    let red1 = &info.literals[info.index];
                    let red2 = &info.literals[info.index + 1];
                    assert!(unifier.unify(base_scope, &base.left, conc_scope, &red1.left));
                    assert!(unifier.unify(base_scope, &base.right, conc_scope, &red2.left));

                    for i in (info.index + 1)..base_clause.literals.len() {
                        let base = &base_clause.literals[i];
                        let red = &info.literals[i + 1];
                        assert!(unifier.unify(base_scope, &base.left, conc_scope, &red.left));
                        assert!(unifier.unify(base_scope, &base.right, conc_scope, &red.right));
                    }

                    // Report the concrete base
                    let map = unifier.into_one_map(base_scope);
                    self.add_var_map(base_id, map, concrete_steps);
                }
            }
            Rule::Extensionality(info) => {
                // For extensionality, the output is always concrete (f = g with no variables).
                // Since there are no variables in the output, we add an empty variable map.
                let base_id = ProofStepId::Active(info.id);
                let map = VariableMap::new();
                self.add_var_map(base_id, map, concrete_steps);
            }
            Rule::Resolution(info) => {
                let long_id = ProofStepId::Active(info.long_id);
                let long_clause = self.get_clause(long_id)?;
                let var_maps = self.reconstruct_trace(
                    &long_clause.literals,
                    traces.as_slice(),
                    &step.clause,
                    conclusion_map,
                    concrete_steps,
                )?;
                for map in var_maps {
                    self.add_var_map(long_id, map, concrete_steps);
                }
            }
            Rule::Specialization(info) => {
                let pattern_id = ProofStepId::Active(info.pattern_id);
                let pattern_clause = self.get_clause(pattern_id)?;
                let var_maps = self.reconstruct_trace(
                    &pattern_clause.literals,
                    traces.as_slice(),
                    &step.clause,
                    conclusion_map,
                    concrete_steps,
                )?;
                for map in var_maps {
                    self.add_var_map(pattern_id, map, concrete_steps);
                }
            }
            rule => {
                return Err(Error::internal(format!(
                    "missing reconstruction method for rule {}",
                    rule.name()
                )));
            }
        }
        Ok(())
    }

    // Reconstructs input var maps given a base, conclusion, and trace.
    //
    // There are two sorts of input: the base clause, and simplifications.
    // When we reconstruct a simplification, we add the appropriate variable map to simp_maps.
    // The base clause is always reconstructed, and we return its var map as the result.
    //
    // If the step cannot be reconstructed, we return an error.
    fn reconstruct_trace(
        &self,
        base_literals: &[FatLiteral],
        traces: &[LiteralTrace],
        conclusion: &FatClause,
        conc_map: VariableMap,
        simp_maps: &mut HashMap<ConcreteStepId, ConcreteStep>,
    ) -> Result<HashSet<VariableMap>, Error> {
        // The unifier will figure out the concrete clauses.
        // The base and conclusion get their own scope.
        let (mut unifier, conc_scope) =
            Unifier::with_map(conc_map, self.normalizer.kernel_context());
        unifier.set_input_context(conc_scope, conclusion.get_local_context());
        let base_scope = unifier.add_scope();
        unifier.set_input_context(base_scope, LocalContext::empty_ref());

        // Each simplification gets its own scope.
        // A proof step gets multiple scopes if it is used for multiple simplifications.
        let mut simp_scopes: HashMap<Scope, ProofStepId> = HashMap::new();

        if traces.len() != base_literals.len() {
            return Err(Error::internal("trace with wrong number of literals"));
        }

        // Do the multi-way unification according to the trace.
        for (base_literal, trace) in base_literals.iter().zip(traces) {
            let (scope, literal, flipped) = match trace {
                LiteralTrace::Eliminated { step, flipped } => {
                    // This matches a one-literal clause.
                    let step_id = ProofStepId::Active(*step);
                    let scope = unifier.add_scope();
                    simp_scopes.insert(scope, step_id);
                    let clause = self.get_clause(step_id)?;
                    unifier.set_input_context(scope, clause.get_local_context());
                    if clause.literals.len() != 1 {
                        // This is two-long-clause resolution.
                        // This should only happen for concrete clauses, and thus we don't
                        // need to unify them.
                        continue;
                    }
                    (scope, &clause.literals[0], *flipped)
                }
                LiteralTrace::Output { index, flipped } => {
                    // The output literal is in the conclusion scope.
                    (conc_scope, &conclusion.literals[*index], *flipped)
                }
                LiteralTrace::Impossible => {
                    continue;
                }
            };

            // For eliminated literals (from simplifications), polarities are opposite.
            // For signed boolean terms (atom = true or atom != true), we just unify the atoms.
            // For equalities, we use the standard literal unification.
            let unified = if base_literal.is_signed_term() && literal.is_signed_term() {
                // Both are signed terms, so just unify the left sides (the atoms)
                unifier.unify(base_scope, &base_literal.left, scope, &literal.left)
            } else {
                // Use standard literal unification
                unifier.unify_literals(base_scope, base_literal, scope, literal, flipped)
            };

            if !unified {
                return Err(Error::internal(format!(
                    "failed to unify base literal {} with trace literal {}",
                    base_literal, literal
                )));
            }
        }

        // Now that we've unified, get the var maps.
        let mut answer = HashSet::new();

        for (scope, map) in unifier.into_maps() {
            if scope == Scope::OUTPUT || scope == conc_scope {
                // We only need to store the scopes for inputs.
                continue;
            }

            if scope == base_scope {
                // This is the base clause, so we return it.
                answer.insert(map);
                continue;
            }

            // This is a simplification, so we store it in simp_maps.
            let step_id = simp_scopes.get(&scope).ok_or_else(|| {
                Error::internal(format!(
                    "no proof step id for scope {:?} in reconstruct_trace",
                    scope
                ))
            })?;
            self.add_var_map(*step_id, map, simp_maps);
        }

        Ok(answer)
    }
}
