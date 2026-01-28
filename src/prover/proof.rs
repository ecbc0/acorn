use std::collections::{HashMap, HashSet};

use crate::certificate::Certificate;
use crate::code_generator::{CodeGenerator, Error};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::kernel::atom::AtomId;
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::Term;
use crate::kernel::variable_map::VariableMap;
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, ProofStepId, Rule};

/// Trait for types that can resolve proof step IDs to clauses.
/// Used by reconstruct_step to look up premises.
///
/// This abstraction allows the same reconstruction logic to be used for:
/// - Full proof reconstruction (via Proof)
/// - Validation at creation time (via ActiveSet)
pub trait ProofResolver {
    fn get_clause(&self, id: ProofStepId) -> Result<&Clause, Error>;
    fn kernel_context(&self) -> &KernelContext;
}

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
}

impl ProofResolver for Proof<'_> {
    fn get_clause(&self, id: ProofStepId) -> Result<&Clause, Error> {
        let step = self.step_map.get(&id).ok_or_else(|| {
            Error::internal(format!(
                "no node found for proof step {:?} in proof graph",
                id
            ))
        })?;
        Ok(&step.clause)
    }

    fn kernel_context(&self) -> &KernelContext {
        self.normalizer.kernel_context()
    }
}

// Each step in the ConcreteProof is associated with a ConcreteStepId.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConcreteStepId {
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
    pub generic: Clause,

    // All of the ways to map the generic variables to concrete ones.
    // Each var_map is paired with the context that its replacement terms reference.
    // This context is needed to look up variable types when specializing.
    pub var_maps: Vec<(VariableMap, LocalContext)>,
}

impl ConcreteStep {
    fn new(generic: Clause, var_map: VariableMap, replacement_context: LocalContext) -> Self {
        ConcreteStep {
            generic,
            var_maps: vec![(var_map, replacement_context)],
        }
    }
}

// Adds a var map for a non-assumption proof step.
fn add_var_map<R: ProofResolver>(
    resolver: &R,
    id: ProofStepId,
    var_map: VariableMap,
    replacement_context: LocalContext,
    concrete_steps: &mut HashMap<ConcreteStepId, ConcreteStep>,
) {
    let generic = resolver.get_clause(id).unwrap();
    match concrete_steps.entry(ConcreteStepId::ProofStep(id)) {
        std::collections::hash_map::Entry::Occupied(mut entry) => {
            let concrete_step = entry.get_mut();
            concrete_step.var_maps.push((var_map, replacement_context));
        }
        std::collections::hash_map::Entry::Vacant(entry) => {
            let concrete_step = ConcreteStep::new(generic.clone(), var_map, replacement_context);
            entry.insert(concrete_step);
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
                // Empty map has no replacement terms, so empty context is fine
                reconstruct_step(
                    self,
                    *id,
                    step,
                    VariableMap::new(),
                    &LocalContext::empty(),
                    &mut concrete_steps,
                )?;
                continue;
            }
            // Multiple concrete instantiations are possible
            let concrete_id = ConcreteStepId::ProofStep(id.clone());
            let var_maps_with_context = match concrete_steps.get(&concrete_id) {
                Some(concrete_step) => concrete_step.var_maps.clone(),
                None => continue,
            };
            for (var_map, context) in var_maps_with_context {
                reconstruct_step(self, *id, step, var_map, &context, &mut concrete_steps)?;
            }
        }

        // Skip the code that comes from concrete assumptions, because we don't need it
        // TODO: should we actually be skipping the original assumptions rather than
        // the simplified versions?
        let mut skip_code = HashSet::new();
        let mut synthetic_definitions = Vec::new();
        for (ps_id, step) in &self.steps {
            let concrete_id = ConcreteStepId::ProofStep(*ps_id);
            if step.rule.is_underlying_assumption() && !step.clause.has_any_variable() {
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
}

// Given a varmap for the conclusion of a proof step, reconstruct varmaps for
// all of its inputs.
// The varmaps represent a concrete clause, in the sense that they provide a mapping to specialize
// the clause into something concrete.
//
// Reconstructed varmaps are added to concrete_steps.
// If the step cannot be reconstructed, we return an error.
//
// The conclusion_map_context is the context that conclusion_map's replacement terms reference.
// This is needed to look up variable types when building output contexts.
pub fn reconstruct_step<R: ProofResolver>(
    resolver: &R,
    id: ProofStepId,
    step: &ProofStep,
    conclusion_map: VariableMap,
    conclusion_map_context: &LocalContext,
    concrete_steps: &mut HashMap<ConcreteStepId, ConcreteStep>,
) -> Result<(), Error> {
    // Some rules we can handle without the traces.
    match &step.rule {
        Rule::PassiveContradiction(_) | Rule::MultipleRewrite(_) => {
            // These rules always use concrete premises, so we can track them without
            // reconstruction logic.
            for id in step.rule.premises() {
                let map = VariableMap::new();
                // Empty context is fine for empty maps
                add_var_map(resolver, id, map, LocalContext::empty(), concrete_steps);
            }
            return Ok(());
        }

        // Rules with populated PremiseMaps: compose raw inference maps with conclusion_map
        // to get concrete var maps. No re-unification needed.
        Rule::Extensionality(_) => {
            // No reconstruction needed - extensionality is sound on universally
            // quantified clauses without instantiation.
            return Ok(());
        }

        Rule::EqualityResolution(_)
        | Rule::EqualityFactoring(_)
        | Rule::Injectivity(_)
        | Rule::BooleanReduction(_)
        | Rule::Rewrite(_)
        | Rule::Resolution(_)
        | Rule::Specialization(_)
        | Rule::Simplification(_)
            if !step.premise_map.is_empty() =>
        {
            let premise_ids = step.rule.premises();
            let mut premise_contexts: Vec<&LocalContext> = Vec::new();
            for premise_id in &premise_ids {
                let premise_clause = resolver.get_clause(*premise_id)?;
                premise_contexts.push(premise_clause.get_local_context());
            }
            let concrete_premises = step.premise_map.concretize_premises(
                &conclusion_map,
                conclusion_map_context,
                &premise_contexts,
            );
            for (premise_id, (mut var_map, mut context)) in
                premise_ids.into_iter().zip(concrete_premises)
            {
                // Fill in any remaining unmapped premise variables with fresh output variables
                let premise_clause = resolver.get_clause(premise_id)?;
                let premise_context = premise_clause.get_local_context();
                let mut next_var = context.len();
                for var_id in 0..premise_context.len() {
                    if !var_map.has_mapping(var_id as AtomId) {
                        if let Some(var_type) = premise_context.get_var_type(var_id) {
                            var_map.set(var_id as AtomId, Term::new_variable(next_var as AtomId));
                            context.set_type(next_var, var_type.clone());
                            next_var += 1;
                        }
                    }
                }
                add_var_map(resolver, premise_id, var_map, context, concrete_steps);
            }

            // For Simplification, also reconstruct the inner step
            if let Rule::Simplification(info) = &step.rule {
                let (inner_map, inner_context) = step.premise_map.inner_step_map(
                    &conclusion_map,
                    conclusion_map_context,
                    info.original.clause.get_local_context(),
                );
                reconstruct_step(
                    resolver,
                    id,
                    &info.original,
                    inner_map,
                    &inner_context,
                    concrete_steps,
                )?;
            }
            return Ok(());
        }

        _ => {}
    }

    match &step.rule {
        Rule::Assumption(info) => {
            if conclusion_map.len() == 0 {
                // No concrete instantiation needed.
                return Ok(());
            }
            // The assumption trace is always identity (each literal maps to itself),
            // so reconstruction just passes through the conclusion_map directly.
            let assumption_id = ConcreteStepId::Assumption(id);
            match concrete_steps.entry(assumption_id) {
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    entry
                        .get_mut()
                        .var_maps
                        .push((conclusion_map, conclusion_map_context.clone()));
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    let generic =
                        Clause::from_literals_unnormalized(info.literals.clone(), &info.context);
                    entry.insert(ConcreteStep::new(
                        generic,
                        conclusion_map,
                        conclusion_map_context.clone(),
                    ));
                }
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

#[cfg(test)]
mod tests {
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::trace::LiteralTrace;
    use crate::proof_step::{ProofStep, Rule, Truthiness};
    use crate::prover::active_set::ActiveSet;

    /// Test that resolution followed by simplification has consistent traces.
    ///
    /// This tests a bug where ResolutionInfo doesn't store the post-resolution literals,
    /// causing reconstruct_trace to use the original long clause literals instead of
    /// the literals after the resolution unifier was applied.
    ///
    /// The scenario:
    /// - Long clause: not g0(x) or g1(x) = c0  (x is a variable)
    /// - Short clause: g0(g2(c1))  (concrete, resolves with first literal, binds x->g2(c1))
    /// - Resolution gives: g1(g2(c1)) = c0
    /// - Simplification clause: g1(g2(x)) != c0  (eliminates g1(g2(c1)) = c0)
    /// - Result: empty clause (contradiction)
    ///
    /// The bug: The trace is built based on the post-resolution clause [g1(g2(c1)) = c0],
    /// but ResolutionInfo only stores short_id and long_id. When reconstruct_trace is called,
    /// it uses long_clause.literals [not g0(x), g1(x) = c0] which don't match the trace
    /// that was built for the post-resolution literals.
    #[test]
    fn test_resolution_with_simplification_trace() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool")
            .parse_constant("g1", "Bool -> Bool")
            .parse_constant("g2", "Bool -> Bool")
            .parse_constant("c0", "Bool")
            .parse_constant("c1", "Bool");

        // Long clause (step 0): not g0(x) or g1(x) = c0
        // First literal is negative (g0(x) != true), second is positive (g1(x) = c0)
        let long_clause = kctx.parse_clause("not g0(x0) or g1(x0) = c0", &["Bool"]);
        let long_step = ProofStep::mock_from_clause(long_clause);

        // Short clause (step 1): g0(g2(c1))
        // This resolves with the first literal of long clause, binding x0 -> g2(c1)
        let short_clause = kctx.parse_clause("g0(g2(c1))", &[]);
        let mut short_step = ProofStep::mock_from_clause(short_clause);
        short_step.truthiness = crate::proof_step::Truthiness::Hypothetical;

        // Simplification clause (step 2): g1(g2(x)) != c0
        // This can eliminate g1(g2(c1)) = c0 from the resolution result
        let simp_clause = kctx.parse_clause("g1(g2(x0)) != c0", &["Bool"]);
        let simp_step = ProofStep::mock_from_clause(simp_clause);

        // Build the active set
        // Order is important: we activate long_step and simp_step first,
        // then call find_resolutions with short_step (which will use next_id = 2)
        let mut active_set = ActiveSet::new();
        active_set.activate(long_step.clone(), &kctx); // Step 0
        active_set.activate(simp_step.clone(), &kctx); // Step 1

        // Find resolutions - short_step will get ID 2 (next_id)
        let mut resolution_results = vec![];
        active_set.find_resolutions(&short_step, &mut resolution_results, &kctx);

        // Now activate short_step so it gets ID 2 (matching what find_resolutions used)
        active_set.activate(short_step.clone(), &kctx); // Step 2

        // Should have at least one resolution result
        assert!(
            !resolution_results.is_empty(),
            "Resolution should produce at least one result. Long: {}, Short: {}",
            long_step.clause,
            short_step.clause
        );

        let resolution_step = resolution_results.into_iter().next().unwrap();

        // The resolution step should have a trace
        assert!(
            resolution_step.trace.is_some(),
            "Resolution step should have a trace"
        );

        // Now simplify the resolution result using the active set
        let simplified_step = active_set.simplify(resolution_step.clone(), &kctx);

        // The simplification should succeed (or not change the step)
        let final_step = simplified_step.unwrap_or(resolution_step);

        // Verify we got the expected structure
        assert!(
            final_step.clause.is_impossible(),
            "Expected empty clause after resolution + simplification, got: {}",
            final_step.clause
        );

        // The final step should be a Simplification wrapping a Resolution
        let simp_info = match &final_step.rule {
            Rule::Simplification(info) => info,
            other => panic!("Expected Simplification rule, got {:?}", other),
        };

        let resolution_info = match &simp_info.original.rule {
            Rule::Resolution(info) => info,
            other => panic!("Expected inner Resolution rule, got {:?}", other),
        };

        // The Simplification step should have a trace mapping from the resolution
        // output to the simplified clause
        let trace = final_step
            .trace
            .as_ref()
            .expect("Expected trace on Simplification step");
        let traces = trace.as_slice();

        // The trace should have entries for the resolution step's clause literals
        assert_eq!(
            traces.len(),
            simp_info.original.clause.literals.len(),
            "Simplification trace should have same length as inner resolution clause literals"
        );

        // Verify ResolutionInfo stores post-resolution literals
        assert!(
            !resolution_info.literals.is_empty(),
            "ResolutionInfo should store post-resolution literals"
        );

        // The simplifying clause should be referenced in the simplification info
        assert!(
            !simp_info.simplifying_ids.is_empty(),
            "Simplification should reference simplifying clause IDs"
        );
    }

    /// Test that resolution with polymorphic simplification uses traced flip correctly.
    ///
    /// This tests a bug where the flip determination in reconstruct_step tries to compute
    /// the flip dynamically using match_terms, rather than using the flip value already
    /// stored in the trace. This fails when both the post-resolution literal and the
    /// simplification literal have variables.
    ///
    /// The scenario:
    /// - Long clause: not g0(x0) or not g1(x0, g2(x0))  (negative literals with variable)
    /// - Short clause: g0(c0)  (concrete, resolves with first literal, binds x0->c0)
    /// - Resolution gives: not g1(c0, g2(c0))
    /// - Simplification clause: g1(x0, g2(x0))  (pattern with variable, eliminates the neg lit)
    /// - Result: empty clause (contradiction)
    ///
    /// The bug: When reconstructing the proof, the code tries to determine if the
    /// simplification literal needs to be flipped relative to the post-resolution literal.
    /// It uses match_terms to test both orientations, but this fails when both literals
    /// have variables (different variable IDs). The fix is to use the `flipped` value
    /// that was already computed and stored in the trace.
    #[test]
    fn test_resolution_simplification_with_polymorphic_flip() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool")
            .parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constant("g2", "Bool -> Bool")
            .parse_constant("c0", "Bool");

        // Long clause (step 0): not g0(x0) or not g1(x0, g2(x0))
        let long_clause = kctx.parse_clause("not g0(x0) or not g1(x0, g2(x0))", &["Bool"]);
        let mut long_step = ProofStep::mock_from_clause(long_clause);
        long_step.truthiness = Truthiness::Factual;

        // Simplification clause (step 1): g1(x0, g2(x0))
        // This pattern will eliminate `not g1(c0, g2(c0))` from the resolution result
        let simp_clause = kctx.parse_clause("g1(x0, g2(x0))", &["Bool"]);
        let simp_step = ProofStep::mock_from_clause(simp_clause);

        // Short clause (step 2): g0(c0)
        // This resolves with the first literal of long clause, binding x0 -> c0
        let short_clause = kctx.parse_clause("g0(c0)", &[]);
        let mut short_step = ProofStep::mock_from_clause(short_clause);
        short_step.truthiness = Truthiness::Hypothetical;

        // Build the active set
        let mut active_set = ActiveSet::new();
        active_set.activate(long_step.clone(), &kctx); // Step 0
        active_set.activate(simp_step.clone(), &kctx); // Step 1

        // Find resolutions - short_step will get ID 2 (next_id)
        let mut resolution_results = vec![];
        active_set.find_resolutions(&short_step, &mut resolution_results, &kctx);

        // Now activate short_step
        active_set.activate(short_step.clone(), &kctx); // Step 2

        assert!(
            !resolution_results.is_empty(),
            "Resolution should produce at least one result"
        );

        let resolution_step = resolution_results.into_iter().next().unwrap();

        // Now simplify the resolution result using the active set
        let simplified_step = active_set.simplify(resolution_step.clone(), &kctx);

        // The simplification should succeed and produce an empty clause
        let final_step = simplified_step.unwrap_or(resolution_step);
        assert!(
            final_step.clause.is_impossible(),
            "Expected empty clause after resolution + simplification, got: {}",
            final_step.clause
        );

        // The final step should be a Simplification wrapping a Resolution
        let simp_info = match &final_step.rule {
            Rule::Simplification(info) => info,
            other => panic!("Expected Simplification rule, got {:?}", other),
        };

        let resolution_info = match &simp_info.original.rule {
            Rule::Resolution(info) => info,
            other => panic!("Expected inner Resolution rule, got {:?}", other),
        };

        // The Simplification step should have a trace
        let trace = final_step
            .trace
            .as_ref()
            .expect("Expected trace on Simplification step");
        let traces = trace.as_slice();

        // Find the simplification trace entry (step 1) in the Simplification step's trace
        let simp_trace = traces
            .iter()
            .find(|t| matches!(t, LiteralTrace::Eliminated { step: 1, .. }));
        assert!(
            simp_trace.is_some(),
            "Expected to find simplification trace entry for step 1"
        );

        // Verify that the trace captures the flip information
        let simp_trace = simp_trace.unwrap();
        if let LiteralTrace::Eliminated { step, flipped } = simp_trace {
            assert_eq!(*step, 1, "Simplification should reference step 1");
            assert!(!flipped, "The simplification literal should not be flipped");
        }

        // Verify the post-resolution literal exists in the inner resolution info
        assert!(
            !resolution_info.literals.is_empty(),
            "ResolutionInfo should store post-resolution literals"
        );
    }
}
