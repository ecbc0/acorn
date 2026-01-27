use std::collections::{HashMap, HashSet};

use crate::certificate::Certificate;
use crate::code_generator::{CodeGenerator, Error};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::trace::LiteralTrace;
use crate::kernel::unifier::{Scope, Unifier};
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
            let (var_maps, output_context) = reconstruct_trace(
                resolver,
                &info.literals,
                &info.context,
                traces.as_slice(),
                &step.clause,
                conclusion_map,
                conclusion_map_context,
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
                        concrete_step
                            .var_maps
                            .push((var_map, output_context.clone()));
                    }
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        // Use from_literals_unnormalized to avoid re-normalizing the clause.
                        // Re-normalizing can change variable IDs if literals sort differently,
                        // which would make the var_map inconsistent with the clause.
                        let generic = Clause::from_literals_unnormalized(
                            info.literals.clone(),
                            &info.context,
                        );
                        let concrete_step =
                            ConcreteStep::new(generic, var_map, output_context.clone());
                        entry.insert(concrete_step);
                    }
                }
            }
        }
        Rule::Rewrite(info) => {
            // For rewrites, the trace applies to the original rewritten literal.
            // We use info.rewritten and info.context which store the pre-normalization
            // literal and its variable context.
            let literals = vec![info.rewritten.clone()];
            let (var_maps, unifier_context) = reconstruct_trace(
                resolver,
                &literals,
                &info.context,
                traces.as_slice(),
                &step.clause,
                conclusion_map,
                conclusion_map_context,
                concrete_steps,
            )?;

            // The target is already concrete, and the conclusion has been made concrete through
            // its variable map. We need to unify the pattern.
            let pattern_id = ProofStepId::Active(info.pattern_id);
            let pattern_clause = &resolver.get_clause(pattern_id)?;
            let pattern = &pattern_clause.literals[0];
            let target_id = ProofStepId::Active(info.target_id);
            let target_clause = &resolver.get_clause(target_id)?;
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
                // Use the unifier's output context from reconstruct_trace, not the step context.
                // The conc_map's replacement terms reference variables in the unifier's output context.
                let output_context = conc_map.build_output_context(&unifier_context);
                let (mut unifier, conc_scope) =
                    Unifier::with_map(conc_map, resolver.kernel_context(), output_context);
                // The conc_scope uses the rewritten literal's context (info.context),
                // because that's what the trace was computed with.
                unifier.set_input_context(conc_scope, &info.context);
                let pattern_scope = unifier.add_scope();
                unifier.set_input_context(pattern_scope, pattern_clause.get_local_context());
                let target_scope = unifier.add_scope();
                unifier.set_input_context(target_scope, target_clause.get_local_context());
                if !unifier.unify(pattern_scope, from_pat, target_scope, &target_subterm) {
                    eprintln!("DEBUG: Unification failed!");
                    eprintln!("  from_pat: {}", from_pat);
                    eprintln!("  target_subterm: {}", target_subterm);
                    eprintln!(
                        "  pattern context: {:?}",
                        pattern_clause.get_local_context()
                    );
                    eprintln!("  target context: {:?}", target_clause.get_local_context());
                    panic!("unification failed");
                }
                assert!(unifier.unify(pattern_scope, to_pat, conc_scope, &rewritten_subterm));

                // Report the concrete pattern
                let (map, map_context) = unifier.into_one_map_with_context(pattern_scope);
                add_var_map(resolver, pattern_id, map, map_context, concrete_steps);
            }

            // The target is already concrete
            let map = VariableMap::new();
            add_var_map(
                resolver,
                target_id,
                map,
                LocalContext::empty(),
                concrete_steps,
            );
        }
        Rule::EqualityFactoring(info) => {
            // For EF, the trace applies to the stored literals.
            let (var_maps, unifier_context) = reconstruct_trace(
                resolver,
                &info.literals,
                &info.context,
                traces.as_slice(),
                &step.clause,
                conclusion_map,
                conclusion_map_context,
                concrete_steps,
            )?;

            // Unify the pre-EF and post-EF literals.
            let base_id = ProofStepId::Active(info.id);
            let base_clause = &resolver.get_clause(base_id)?;
            assert!(base_clause.literals.len() == info.literals.len());

            for conc_map in var_maps {
                let output_context = conc_map.build_output_context(&unifier_context);
                let (mut unifier, conc_scope) =
                    Unifier::with_map(conc_map, resolver.kernel_context(), output_context);
                unifier.set_input_context(conc_scope, &info.context);
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
                let (map, map_context) = unifier.into_one_map_with_context(base_scope);
                add_var_map(resolver, base_id, map, map_context, concrete_steps);
            }
        }
        Rule::EqualityResolution(info) => {
            // For ER, the trace applies to the stored literals.
            let (var_maps, unifier_context) = reconstruct_trace(
                resolver,
                &info.literals,
                &info.context,
                traces.as_slice(),
                &step.clause,
                conclusion_map,
                conclusion_map_context,
                concrete_steps,
            )?;

            // Unify the pre-ER and post-ER literals.
            let base_id = ProofStepId::Active(info.id);
            let base_clause = &resolver.get_clause(base_id)?;
            assert!(base_clause.literals.len() == info.literals.len() + 1);

            for conc_map in var_maps {
                let output_context = conc_map.build_output_context(&unifier_context);
                let (mut unifier, conc_scope) =
                    Unifier::with_map(conc_map, resolver.kernel_context(), output_context);
                unifier.set_input_context(conc_scope, &info.context);
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
                let (map, map_context) = unifier.into_one_map_with_context(base_scope);
                add_var_map(resolver, base_id, map, map_context, concrete_steps);
            }
        }
        Rule::Injectivity(info) => {
            // For injectivity, the trace applies to the stored literals.
            let (var_maps, unifier_context) = reconstruct_trace(
                resolver,
                &info.literals,
                &info.context,
                traces.as_slice(),
                &step.clause,
                conclusion_map,
                conclusion_map_context,
                concrete_steps,
            )?;

            // Unify the pre-injectivity and post-injectivity literals.
            let base_id = ProofStepId::Active(info.id);
            let base_clause = &resolver.get_clause(base_id)?;
            assert!(base_clause.literals.len() == info.literals.len());

            for conc_map in var_maps {
                let output_context = conc_map.build_output_context(&unifier_context);
                let (mut unifier, conc_scope) =
                    Unifier::with_map(conc_map, resolver.kernel_context(), output_context);
                unifier.set_input_context(conc_scope, &info.context);
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
                let (map, map_context) = unifier.into_one_map_with_context(base_scope);
                add_var_map(resolver, base_id, map, map_context, concrete_steps);
            }
        }
        Rule::BooleanReduction(info) => {
            // For boolean reduction, the trace applies to the stored literals.
            let (var_maps, unifier_context) = reconstruct_trace(
                resolver,
                &info.literals,
                &info.context,
                traces.as_slice(),
                &step.clause,
                conclusion_map,
                conclusion_map_context,
                concrete_steps,
            )?;

            // Unify the pre-reduction and post-reduction literals.
            let base_id = ProofStepId::Active(info.id);
            let base_clause = &resolver.get_clause(base_id)?;
            assert!(base_clause.literals.len() + 1 == info.literals.len());

            for conc_map in var_maps {
                let output_context = conc_map.build_output_context(&unifier_context);
                let (mut unifier, conc_scope) =
                    Unifier::with_map(conc_map, resolver.kernel_context(), output_context);
                unifier.set_input_context(conc_scope, &info.context);
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
                let (map, map_context) = unifier.into_one_map_with_context(base_scope);
                add_var_map(resolver, base_id, map, map_context, concrete_steps);
            }
        }
        Rule::Extensionality(_) => {
            // For extensionality, we don't need to add the source clause to concrete_steps.
            // The extensionality inference is sound on the universally quantified clause directly:
            // from "forall x. f(x) = g(x)" we derive "f = g" without needing to instantiate x.
            // This avoids requiring a witness for types that may be uninhabited.
        }
        Rule::Resolution(info) => {
            // For Resolution, we do custom reconstruction because the trace was
            // built for post-resolution literals, but simplifications reference
            // those post-resolution literals (not the original long_clause literals).
            //
            // We handle this by:
            // 1. For Eliminated entries that reference the short clause: use long_clause literal
            // 2. For Eliminated entries that reference simplification steps: use post-resolution literal
            // 3. For Output entries: use post-resolution literal (mapped to conclusion)

            let long_id = ProofStepId::Active(info.long_id);
            let long_clause = resolver.get_clause(long_id)?;
            let short_id = ProofStepId::Active(info.short_id);
            let short_clause = resolver.get_clause(short_id)?;
            let traces_slice = traces.as_slice();

            // Build a unifier that handles all scopes
            let output_context = conclusion_map.build_output_context(conclusion_map_context);
            let (mut unifier, conc_scope) =
                Unifier::with_map(conclusion_map, resolver.kernel_context(), output_context);
            unifier.set_input_context(conc_scope, step.clause.get_local_context());

            let long_scope = unifier.add_scope();
            unifier.set_input_context(long_scope, long_clause.get_local_context());

            let post_res_scope = unifier.add_scope();
            unifier.set_input_context(post_res_scope, &info.context);

            let short_scope = if short_clause.literals.len() == 1 {
                let scope = unifier.add_scope();
                unifier.set_input_context(scope, short_clause.get_local_context());
                Some(scope)
            } else {
                None
            };

            // Track simplification scopes - each occurrence needs its own scope
            // because the same simp step might eliminate multiple literals with
            // different substitutions.
            let mut simp_scopes: Vec<(usize, Scope)> = Vec::new();

            // IMPORTANT: Process Eliminated traces FIRST, before Output traces.
            // This is necessary because:
            // 1. Eliminated traces unify long_scope with short_scope
            // 2. Output traces unify long_scope with post_res_scope
            // If we process Output traces first, long_scope variables get mapped to
            // OUTPUT variables with types from the long clause context.
            // Then when we process Eliminated traces, short_scope variables create
            // NEW OUTPUT variables with types from the short clause context.
            // If these types differ (common in polymorphic code), unification fails.
            // By processing Eliminated first, short_scope and long_scope variables
            // get unified together before post_res_scope comes into play.
            for (i, res_trace) in info.resolution_trace.iter().enumerate() {
                if let LiteralTrace::Eliminated { flipped, .. } = res_trace {
                    // This literal was resolved with the short clause
                    if let Some(short_scope) = short_scope {
                        let long_lit = &long_clause.literals[i];
                        let short_lit = &short_clause.literals[0];

                        if !unifier.unify_literals(
                            long_scope,
                            long_lit,
                            short_scope,
                            short_lit,
                            *flipped,
                        ) {
                            return Err(Error::internal(format!(
                                "failed to unify resolved literal {} with short clause {}",
                                long_lit, short_lit
                            )));
                        }
                    }
                }
            }

            // Now process Output traces (and handle final_trace for simplifications)
            for (i, (res_trace, final_trace)) in info
                .resolution_trace
                .iter()
                .zip(traces_slice.iter())
                .enumerate()
            {
                match res_trace {
                    LiteralTrace::Eliminated { .. } => {
                        // Already processed above
                    }
                    LiteralTrace::Output {
                        index: post_res_idx,
                        flipped: res_flip,
                    } => {
                        // Unify long_clause[i] with post_res[post_res_idx]
                        let long_lit = &long_clause.literals[i];
                        let post_res_lit = &info.literals[*post_res_idx];

                        if !unifier.unify_literals(
                            long_scope,
                            long_lit,
                            post_res_scope,
                            post_res_lit,
                            *res_flip,
                        ) {
                            return Err(Error::internal(format!(
                                "failed to unify long clause literal {} with post-resolution literal {}",
                                long_lit, post_res_lit
                            )));
                        }

                        // Now handle what happened to this post-resolution literal
                        match final_trace {
                            LiteralTrace::Output {
                                index: final_idx,
                                flipped: final_flip,
                            } => {
                                // Post-res literal made it to the conclusion
                                // Combine the flips: long→post_res was res_flip, but we're now
                                // relating post_res→conclusion
                                let conc_lit = &step.clause.literals[*final_idx];
                                if !unifier.unify_literals(
                                    post_res_scope,
                                    post_res_lit,
                                    conc_scope,
                                    conc_lit,
                                    *final_flip != *res_flip,
                                ) {
                                    return Err(Error::internal(format!(
                                        "failed to unify post-res literal {} with conclusion {}",
                                        post_res_lit, conc_lit
                                    )));
                                }
                            }
                            LiteralTrace::Eliminated {
                                step: simp_id,
                                flipped: composed_flip,
                            } => {
                                // Post-res literal was eliminated by simplification.
                                // The composed_flip is the flip from long_clause[i] to the simp literal.
                                // We need the flip from post_res to simp, which is composed_flip XOR res_flip.
                                let simp_step_id = ProofStepId::Active(*simp_id);
                                let simp_clause = resolver.get_clause(simp_step_id)?;
                                if simp_clause.literals.len() == 1 {
                                    // Create a new scope for this occurrence
                                    let simp_scope = unifier.add_scope();
                                    unifier.set_input_context(
                                        simp_scope,
                                        simp_clause.get_local_context(),
                                    );
                                    simp_scopes.push((*simp_id, simp_scope));
                                    let simp_lit = &simp_clause.literals[0];

                                    // XOR the composed flip with res_flip to get the flip
                                    // from post_res to simp (same pattern as the Output case above)
                                    let flip_to_use = *composed_flip != *res_flip;
                                    if !unifier.unify_literals(
                                        post_res_scope,
                                        post_res_lit,
                                        simp_scope,
                                        simp_lit,
                                        flip_to_use,
                                    ) {
                                        return Err(Error::internal(format!(
                                                "failed to unify post-res literal {} with simp literal {} (flip={})",
                                                post_res_lit, simp_lit, flip_to_use
                                            )));
                                    }
                                }
                            }
                            LiteralTrace::Impossible => {}
                        }
                    }
                    LiteralTrace::Impossible => {}
                }
            }

            // Extract all maps and add to concrete_steps
            let (all_maps, output_ctx) = unifier.into_maps_with_context();
            for (scope, var_map) in all_maps {
                if scope == long_scope {
                    add_var_map(
                        resolver,
                        long_id,
                        var_map,
                        output_ctx.clone(),
                        concrete_steps,
                    );
                } else if Some(scope) == short_scope {
                    add_var_map(
                        resolver,
                        short_id,
                        var_map,
                        output_ctx.clone(),
                        concrete_steps,
                    );
                } else if let Some((simp_id, _)) = simp_scopes.iter().find(|(_, s)| *s == scope) {
                    let simp_step_id = ProofStepId::Active(*simp_id);
                    add_var_map(
                        resolver,
                        simp_step_id,
                        var_map,
                        output_ctx.clone(),
                        concrete_steps,
                    );
                }
                // conc_scope and post_res_scope are not added to concrete_steps
            }

            // For multi-literal short clauses, we didn't create a scope for them above.
            // We still need to track them with an empty var_map so they appear in the certificate.
            if short_scope.is_none() && short_clause.literals.len() > 1 {
                add_var_map(
                    resolver,
                    short_id,
                    VariableMap::new(),
                    output_ctx,
                    concrete_steps,
                );
            }
        }
        Rule::Specialization(info) => {
            let pattern_id = ProofStepId::Active(info.pattern_id);
            let pattern_clause = resolver.get_clause(pattern_id)?;
            let (var_maps, output_context) = reconstruct_trace(
                resolver,
                &pattern_clause.literals,
                pattern_clause.get_local_context(),
                traces.as_slice(),
                &step.clause,
                conclusion_map,
                conclusion_map_context,
                concrete_steps,
            )?;
            for map in var_maps {
                add_var_map(
                    resolver,
                    pattern_id,
                    map,
                    output_context.clone(),
                    concrete_steps,
                );
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
/// Returns (var_maps, output_context) where output_context is the context
/// that the VariableMaps' replacement terms reference. This context
/// must be used when calling build_output_context on the returned maps.
///
/// The conc_map_context is the context that conc_map's replacement terms reference.
/// This is needed to look up variable types when building output contexts.
fn reconstruct_trace<R: ProofResolver>(
    resolver: &R,
    base_literals: &[Literal],
    base_context: &LocalContext,
    traces: &[LiteralTrace],
    conclusion: &Clause,
    conc_map: VariableMap,
    conc_map_context: &LocalContext,
    simp_maps: &mut HashMap<ConcreteStepId, ConcreteStep>,
) -> Result<(HashSet<VariableMap>, LocalContext), Error> {
    // The unifier will figure out the concrete clauses.
    // The base and conclusion get their own scope.
    let output_context = conc_map.build_output_context(conc_map_context);
    let (mut unifier, conc_scope) =
        Unifier::with_map(conc_map, resolver.kernel_context(), output_context);
    unifier.set_input_context(conc_scope, conclusion.get_local_context());
    let base_scope = unifier.add_scope();
    unifier.set_input_context(base_scope, base_context);

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
                let clause = resolver.get_clause(step_id)?;
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

    // Now that we've unified, get the var maps and output context.
    // The output context is needed for build_output_context calls.
    let mut answer = HashSet::new();
    let (maps, unifier_output_context) = unifier.into_maps_with_context();

    for (scope, map) in maps {
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
        add_var_map(
            resolver,
            *step_id,
            map,
            unifier_output_context.clone(),
            simp_maps,
        );
    }

    Ok((answer, unifier_output_context))
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

        // Get the resolution info
        let resolution_info = match &final_step.rule {
            Rule::Resolution(info) => info,
            other => panic!("Expected Resolution rule, got {:?}", other),
        };

        // The trace should have entries for the long clause's literals
        let trace = final_step.trace.as_ref().expect("Expected trace");
        let traces = trace.as_slice();

        // Here's the key invariant that should hold but doesn't due to the bug:
        // The trace was built based on the POST-resolution clause, which has
        // only ONE literal (g1(g2(c1)) = c0) - the first literal was eliminated by resolution.
        //
        // But ResolutionInfo only stores long_id, and reconstruct_step uses
        // long_clause.literals which has TWO literals.
        //
        // The trace length should match what reconstruct_step expects (long_clause.literals.len())
        // but the trace was built for post-resolution literals.

        // Verify ResolutionInfo now stores post-resolution literals
        assert!(
            !resolution_info.literals.is_empty(),
            "ResolutionInfo should store post-resolution literals"
        );

        // The trace has entries for all the original literals
        let long_clause_for_reconstruction = &active_set.get_step(resolution_info.long_id).clause;
        let long_literal_count = long_clause_for_reconstruction.literals.len();
        assert_eq!(
            traces.len(),
            long_literal_count,
            "Trace should have same length as long clause literals"
        );

        // Find the simplification trace entry
        let simp_trace_idx = traces
            .iter()
            .position(|t| matches!(t, LiteralTrace::Eliminated { step, .. } if *step == 1));
        let simp_trace_idx = simp_trace_idx.expect("Expected to find simplification trace entry");

        // Find the corresponding post-resolution literal using the resolution_trace.
        // The resolution_trace maps original literal indices to post-resolution literal indices.
        let post_res_index = match &resolution_info.resolution_trace[simp_trace_idx] {
            LiteralTrace::Output { index, .. } => *index,
            other => panic!(
                "Expected Output trace for simplified literal, got {:?}",
                other
            ),
        };
        let post_res_literal = &resolution_info.literals[post_res_index];
        let simp_literal = &simp_step.clause.literals[0];

        // The post-resolution literal should be unifiable with the simplification literal.
        // This is what our fix enables - we now use post-resolution literals for reconstruction.
        use crate::kernel::variable_map::VariableMap;
        let post_res_context = &resolution_info.context;
        let simp_context = simp_step.clause.get_local_context();

        let mut var_map = VariableMap::new();
        let can_match_left = var_map.match_terms(
            simp_literal.left.as_ref(),
            post_res_literal.left.as_ref(),
            simp_context,
            post_res_context,
            &kctx,
        );
        let can_match_right = can_match_left
            && var_map.match_terms(
                simp_literal.right.as_ref(),
                post_res_literal.right.as_ref(),
                simp_context,
                post_res_context,
                &kctx,
            );

        assert!(
            can_match_right,
            "Post-resolution literal should be unifiable with simplification literal.\n\
             Post-resolution literal: {}\n\
             Simplification literal: {}\n\
             This verifies the fix: ResolutionInfo now stores post-resolution literals.",
            post_res_literal, simp_literal
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

        // Get the resolution info
        let resolution_info = match &final_step.rule {
            Rule::Resolution(info) => info,
            other => panic!("Expected Resolution rule, got {:?}", other),
        };

        // The trace should have a simplification entry with the flipped value set
        let trace = final_step.trace.as_ref().expect("Expected trace");
        let traces = trace.as_slice();

        // Find the simplification trace entry (step 1)
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
            // The flipped value should be correctly tracked (false in this case because
            // g1(x0, g2(x0)) matches g1(c0, g2(c0)) without flipping)
            assert!(!flipped, "The simplification literal should not be flipped");
        }

        // Verify the post-resolution literal exists
        assert!(
            !resolution_info.literals.is_empty(),
            "ResolutionInfo should store post-resolution literals"
        );
    }
}
