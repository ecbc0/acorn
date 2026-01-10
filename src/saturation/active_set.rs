use std::collections::{HashMap, HashSet};

use super::rewrite_tree::{Rewrite, RewriteTree};
use crate::kernel::clause::Clause;
use crate::kernel::clause_set::TermId;
use crate::kernel::fingerprint::FingerprintUnifier;
use crate::kernel::inference;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::pdt::LiteralSet;
use crate::kernel::term::{PathStep, Term};
use crate::kernel::trace::{ClauseTrace, LiteralTrace};
use crate::kernel::unifier::{Scope, Unifier};
use crate::kernel::{EqualityGraph, StepId};
use crate::proof_step::{
    BooleanReductionInfo, EqualityFactoringInfo, EqualityResolutionInfo, ExtensionalityInfo,
    InjectivityInfo, ProofStep, Rule, Truthiness,
};

/// The ActiveSet stores a bunch of clauses that are indexed for various efficient lookups.
/// The goal is that, given a new clause, it is efficient to determine what can be concluded
/// given that clause and one clause from the active set.
/// "Efficient" is relative - this still may take time roughly linear to the size of the active set.
#[derive(Clone)]
pub struct ActiveSet {
    // A vector for indexed reference
    steps: Vec<ProofStep>,

    // The long clauses (ie more than one literal) that we have proven.
    long_clauses: HashSet<Clause>,

    // The short clauses (ie just one literal) that we have proven.
    literal_set: LiteralSet,

    // An index of all the positive literals that we can do resolution with.
    positive_res_targets: FingerprintUnifier<ResolutionTarget>,

    // An index of all the negative literals that we can do resolution with.
    negative_res_targets: FingerprintUnifier<ResolutionTarget>,

    // A graph that encodes equalities and inequalities between terms.
    pub graph: EqualityGraph,

    // Information about every subterm that appears in an activated concrete literal,
    // except "true".
    subterms: Vec<SubtermInfo>,

    // An index to find the id of a subterm for an exact match.
    subterm_map: HashMap<Term, usize>,

    // An index to find the id of subterms for a pattern match.
    subterm_unifier: FingerprintUnifier<usize>,

    // A data structure to do the mechanical rewriting of subterms.
    rewrite_tree: RewriteTree,
}

/// A ResolutionTarget represents a literal that we could do resolution with.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ResolutionTarget {
    // Which proof step the resolution target is in.
    step_index: usize,

    // Which literal within the clause the resolution target is in.
    literal_index: usize,

    // Whether we index starting with the left term of the literal.
    // (As opposed to the right term.)
    left: bool,
}

/// Information about a subterm that appears in an activated concrete literal.
#[derive(Clone)]
struct SubtermInfo {
    // The subterm itself
    term: Term,

    // Where the subterm occurs, in activated concrete literals.
    locations: Vec<SubtermLocation>,

    // The possible terms that this subterm can be rewritten to.
    // Note that this contains duplicates.
    // We do use duplicates to prevent factual-factual rewrites, but it is displeasing.
    rewrites: Vec<Rewrite>,

    // The inspiration id for a subterm is the first activated concrete proof step that contains it.
    inspiration_id: usize,
}

/// A SubtermLocation describes somewhere that the subterm exists among the activated clauses.
/// Subterm locations always refer to concrete single-literal clauses.
#[derive(Clone)]
struct SubtermLocation {
    // Which proof step the subterm is in.
    // The literal can be either positive or negative.
    target_id: usize,

    // Whether the subterm is in the left term of the literal.
    // (As opposed to the right one.)
    left: bool,

    // The path from the root term to the subterm.
    // Uses PathStep::Function/Argument to navigate the curried term structure.
    // An empty path means the root, so the whole term is the relevant subterm.
    path: Vec<PathStep>,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet {
            steps: vec![],
            long_clauses: HashSet::new(),
            literal_set: LiteralSet::new(),
            positive_res_targets: FingerprintUnifier::new(),
            negative_res_targets: FingerprintUnifier::new(),
            graph: EqualityGraph::new(),
            subterms: vec![],
            subterm_map: HashMap::new(),
            subterm_unifier: FingerprintUnifier::new(),
            rewrite_tree: RewriteTree::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }

    fn is_known_long_clause(&self, clause: &Clause) -> bool {
        clause.literals.len() > 1 && self.long_clauses.contains(clause)
    }

    /// Finds all resolutions that can be done with a given proof step.
    /// The "new clause" is the one that is being activated, and the "old clause" is the existing one.
    pub fn find_resolutions(
        &self,
        new_step: &ProofStep,
        output: &mut Vec<ProofStep>,
        kernel_context: &KernelContext,
    ) {
        let new_step_id = self.next_id();
        for (i, new_literal) in new_step.clause.literals.iter().enumerate() {
            let target_map = if new_literal.positive {
                &self.negative_res_targets
            } else {
                &self.positive_res_targets
            };

            let targets = target_map.find_unifying(
                &new_literal.left,
                new_step.clause.get_local_context(),
                kernel_context,
            );
            for target in targets {
                let old_step = self.get_step(target.step_index);
                let flipped = !target.left;

                if new_step.truthiness == Truthiness::Factual
                    && old_step.truthiness == Truthiness::Factual
                {
                    // No global-global resolution
                    continue;
                }

                let step = if new_literal.positive {
                    self.try_resolution(
                        new_step_id,
                        new_step,
                        i,
                        target.step_index,
                        old_step,
                        target.literal_index,
                        flipped,
                        kernel_context,
                    )
                } else {
                    self.try_resolution(
                        target.step_index,
                        old_step,
                        target.literal_index,
                        new_step_id,
                        new_step,
                        i,
                        flipped,
                        kernel_context,
                    )
                };

                if let Some(step) = step {
                    output.push(step);
                }
            }
        }
    }

    /// Tries to do a resolution from two clauses. This works when two literals can be unified
    /// in such a way that they contradict each other.
    ///
    /// There are two ways that A = B and C != D can contradict.
    /// When u(A) = u(C) and u(B) = u(D), that is "not flipped".
    /// When u(A) = u(D) and u(B) = u(C), that is "flipped".
    ///
    /// To do resolution, one of the literals must be positive, and the other must be negative.
    fn try_resolution(
        &self,
        pos_id: usize,
        pos_step: &ProofStep,
        pos_index: usize,
        neg_id: usize,
        neg_step: &ProofStep,
        neg_index: usize,
        flipped: bool,
        kernel_context: &KernelContext,
    ) -> Option<ProofStep> {
        let pos_clause = &pos_step.clause;
        assert!(pos_clause.literals[pos_index].positive);

        let neg_clause = &neg_step.clause;
        assert!(!neg_clause.literals[neg_index].positive);

        // Figure out which of the positive and negative clauses are long and short.
        let (short_id, short_step, short_index, long_id, long_step, long_index) =
            if pos_clause.len() < neg_clause.len() {
                (pos_id, pos_step, pos_index, neg_id, neg_step, neg_index)
            } else {
                (neg_id, neg_step, neg_index, pos_id, pos_step, pos_index)
            };
        let short_clause = &short_step.clause;
        let long_clause = &long_step.clause;

        // Do some heuristic filtering before trying unification, because unification is expensive.

        // We do only the simplest form of two-long-clause resolution.
        // Concluding from concrete "A or B" and "not A or B" that "B" is true.
        // So let's allow that case, and return None otherwise.
        if short_clause.len() > 1 {
            if short_clause.len() != 2 || long_clause.len() != 2 {
                return None;
            }
            if short_clause.has_any_variable() || long_clause.has_any_variable() {
                return None;
            }
        }

        // Check the non-matching short literal.
        // This code would support short clauses longer than two literals, if we wanted.
        for (i, literal) in short_clause.literals.iter().enumerate() {
            if i == short_index {
                continue;
            }
            if literal.has_any_variable() {
                return None;
            }
            if let Some(index) = long_clause.literals.iter().position(|lit| lit == literal) {
                if index == long_index {
                    // This is a weird case. Two different literals in the short clause
                    // match the same literal in the long clause.
                    return None;
                }

                // This is the good case, where the other parts of the short clause match
                // things already in the long clause, thus we can ignore them
                continue;
            }
            return None;
        }

        // Heuristics done. Let's unify.
        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, short_clause.get_local_context());
        unifier.set_input_context(Scope::RIGHT, long_clause.get_local_context());

        // The short clause is "left" scope and the long clause is "right" scope.
        // This is different from the "left" and "right" of the literals - unfortunately
        // "left" and "right" are a bit overloaded here.
        let short_a = &short_clause.literals[short_index].left;
        let short_b = &short_clause.literals[short_index].right;
        let (long_a, long_b) = if flipped {
            (
                &long_clause.literals[long_index].right,
                &long_clause.literals[long_index].left,
            )
        } else {
            (
                &long_clause.literals[long_index].left,
                &long_clause.literals[long_index].right,
            )
        };
        if !unifier.unify(Scope::LEFT, short_a, Scope::RIGHT, long_a) {
            return None;
        }
        if !unifier.unify(Scope::LEFT, short_b, Scope::RIGHT, long_b) {
            return None;
        }

        let mut literals = vec![];
        let mut incremental_trace = vec![];
        for (i, literal) in long_clause.literals.iter().enumerate() {
            if i == long_index {
                incremental_trace.push(LiteralTrace::Eliminated {
                    step: short_id,
                    flipped,
                });
                continue;
            }
            let index = literals.len();
            let left = unifier.apply(Scope::RIGHT, &literal.left);
            let right = unifier.apply(Scope::RIGHT, &literal.right);
            let (new_literal, new_flip) = Literal::new_with_flip(literal.positive, left, right);
            literals.push(new_literal);
            incremental_trace.push(LiteralTrace::Output {
                index,
                flipped: new_flip,
            });
        }

        // Gather the output data
        let context = unifier.take_output_context();

        // Store post-resolution literals and trace for reconstruction.
        // These are needed because simplification operates on post-resolution literals,
        // but the composed trace maps from original long_clause literals.
        let resolution_literals = literals.clone();
        let resolution_context = context.clone();
        let resolution_trace = incremental_trace.clone();

        let (clause, trace) =
            Clause::new_with_trace(literals, ClauseTrace::new(incremental_trace), &context);
        let mut step = ProofStep::resolution(
            long_id,
            long_step,
            short_id,
            short_step,
            clause,
            resolution_literals,
            resolution_context,
            resolution_trace,
        );
        step.trace = Some(trace);
        Some(step)
    }

    /// Look for ways to rewrite a literal that is not yet in the active set.
    /// The literal must be concrete.
    /// The naming convention is that we use the pattern s->t to rewrite u in u ?= v.
    pub fn activate_rewrite_target(
        &mut self,
        target_id: usize,
        target_step: &ProofStep,
        output: &mut Vec<ProofStep>,
        kernel_context: &KernelContext,
    ) {
        assert!(target_step.clause.len() == 1);
        let target_literal = &target_step.clause.literals[0];

        for (target_left, u, _) in target_literal.both_term_pairs() {
            let u_subterms = u.rewritable_subterms_with_paths();

            for (path, u_subterm) in u_subterms {
                // Skip subterms whose types contain BoundVariables (e.g., bare polymorphic constants).
                // These can't be meaningfully rewritten without type instantiation.
                let subterm_type =
                    u_subterm.get_type_with_context(LocalContext::empty_ref(), kernel_context);
                if subterm_type.has_bound_variable() {
                    continue;
                }

                let u_subterm_id = if let Some(id) = self.subterm_map.get(&u_subterm) {
                    // We already have data for this subterm.
                    *id
                } else {
                    // We've never seen this subterm before.
                    // We need to find all the possible rewrites for it.
                    // Note: concrete terms (no variables), so empty local context is safe.
                    let rewrites = self.rewrite_tree.get_rewrites(
                        &u_subterm,
                        0,
                        LocalContext::empty_ref(),
                        kernel_context,
                    );

                    // Add these rewrites to the term graph (only if both terms are concrete)
                    let id1 = self.graph.insert_term(&u_subterm, kernel_context);
                    for rewrite in &rewrites {
                        // rewrite.term may have variables if the pattern had variables
                        // that weren't fully matched. Only add to term graph if concrete.
                        if !rewrite.term.has_any_variable() {
                            let id2 = self.graph.insert_term(&rewrite.term, kernel_context);
                            self.add_to_term_graph(
                                rewrite.pattern_id,
                                Some(target_id),
                                id1,
                                id2,
                                rewrite.forwards,
                                true,
                            );
                        }
                    }

                    // Populate the subterm info.
                    let id = self.subterms.len();
                    self.subterms.push(SubtermInfo {
                        term: u_subterm.clone(),
                        locations: vec![],
                        rewrites,
                        inspiration_id: target_id,
                    });
                    self.subterm_map.insert(u_subterm.clone(), id);
                    // Subterms are concrete (no variables), so empty local context is safe
                    self.subterm_unifier.insert(
                        &u_subterm,
                        id,
                        LocalContext::empty_ref(),
                        kernel_context,
                    );
                    id
                };

                // Apply all the ways to rewrite u_subterm.
                for rewrite in &self.subterms[u_subterm_id].rewrites {
                    if target_id == rewrite.pattern_id {
                        // Don't rewrite a literal with itself
                        continue;
                    }

                    let pattern_step = self.get_step(rewrite.pattern_id);
                    if target_step.truthiness == Truthiness::Factual
                        && pattern_step.truthiness == Truthiness::Factual
                    {
                        // No global-global rewriting
                        continue;
                    }

                    let ps = ProofStep::rewrite(
                        rewrite.pattern_id,
                        &pattern_step,
                        target_id,
                        target_step,
                        target_left,
                        &path,
                        rewrite.forwards,
                        &rewrite.term,
                        &rewrite.context,
                    );
                    output.push(ps);
                }

                // Record the location of this subterm.
                self.subterms[u_subterm_id].locations.push(SubtermLocation {
                    target_id,
                    left: target_left,
                    path,
                });
            }
        }
    }

    /// When we have a new rewrite pattern, find everything that we can rewrite with it.
    /// The naming convention is that we use the pattern s->t to rewrite u in u ?= v.
    pub fn activate_rewrite_pattern(
        &mut self,
        pattern_id: usize,
        pattern_step: &ProofStep,
        output: &mut Vec<ProofStep>,
        kernel_context: &KernelContext,
    ) {
        assert!(pattern_step.clause.len() == 1);
        let pattern_literal = &pattern_step.clause.literals[0];
        assert!(pattern_literal.positive);

        for (forwards, s, t) in pattern_literal.both_term_pairs() {
            if s.is_true() {
                // Don't rewrite from "true"
                continue;
            }

            // Look for existing subterms that match s
            // Note: s comes from the pattern clause, subterms are concrete
            let subterm_ids: Vec<usize> = self
                .subterm_unifier
                .find_unifying(s, pattern_step.clause.get_local_context(), kernel_context)
                .iter()
                .map(|&x| *x)
                .collect();

            for subterm_id in subterm_ids {
                let subterm_info = &self.subterms[subterm_id];
                let subterm = &subterm_info.term;

                let mut unifier = Unifier::new(3, kernel_context);
                unifier.set_input_context(Scope::LEFT, pattern_step.clause.get_local_context());
                // Subterms are concrete (no variables), so empty local context is fine
                unifier.set_input_context(Scope::RIGHT, LocalContext::empty_ref());
                if !unifier.unify(Scope::LEFT, s, Scope::RIGHT, subterm) {
                    continue;
                }
                let new_subterm = unifier.apply(Scope::LEFT, t);
                let new_subterm_context = unifier.output_context().clone();

                for location in &subterm_info.locations {
                    if location.target_id == pattern_id {
                        // Don't rewrite a literal with itself
                        continue;
                    }
                    let target_id = location.target_id;
                    let target_step = self.get_step(target_id);

                    if pattern_step.truthiness == Truthiness::Factual
                        && target_step.truthiness == Truthiness::Factual
                    {
                        // No global-global rewriting
                        continue;
                    }

                    let ps = ProofStep::rewrite(
                        pattern_id,
                        pattern_step,
                        target_id,
                        target_step,
                        location.left,
                        &location.path,
                        forwards,
                        &new_subterm,
                        &new_subterm_context,
                    );
                    output.push(ps);
                }

                // Add this rewrite to the term graph.
                // Only add to term graph if both terms are concrete (no variables).
                // The subterm is always concrete, but new_subterm may have variables
                // if the pattern had variables that weren't fully unified.
                if !new_subterm.has_any_variable() {
                    let id1 = self.graph.insert_term(&subterm, kernel_context);
                    let id2 = self.graph.insert_term(&new_subterm, kernel_context);
                    self.add_to_term_graph(
                        pattern_id,
                        Some(subterm_info.inspiration_id),
                        id1,
                        id2,
                        forwards,
                        true,
                    );
                }

                self.subterms[subterm_id].rewrites.push(Rewrite {
                    pattern_id,
                    forwards,
                    term: new_subterm,
                    context: new_subterm_context,
                });
            }
        }
    }

    /// Tries to do inference using the equality resolution (ER) rule.
    /// Specifically, when one literal is of the form
    ///   u != v
    /// then if we can unify u and v, we can eliminate this literal from the clause.
    pub fn equality_resolution(
        activated_id: usize,
        activated_step: &ProofStep,
        kernel_context: &KernelContext,
    ) -> Vec<ProofStep> {
        let clause = &activated_step.clause;
        let mut answer = vec![];

        // Use the new method to find all possible equality resolutions
        for (index, new_literals, flipped, context) in
            inference::find_equality_resolutions(clause, kernel_context)
        {
            let literals = new_literals.clone();
            let (new_clause, traces) = Clause::normalize_with_trace(new_literals, &context);

            // Check if normalization resulted in a tautology
            if !new_clause.is_tautology() {
                let step = ProofStep::direct(
                    activated_id,
                    activated_step,
                    Rule::EqualityResolution(EqualityResolutionInfo {
                        id: activated_id,
                        index,
                        literals,
                        context,
                        flipped,
                    }),
                    new_clause,
                    traces,
                );
                answer.push(step);
            }
        }

        answer
    }

    /// Tries to do inference using the function elimination (FE) rule.
    /// Note that I just made up this rule, it isn't part of standard superposition.
    /// Apply injectivity to derive inequalities from function inequalities.
    /// When f(a, b, d) != f(a, c, d), that implies that b != c.
    /// We can run this operation on any negative literal in the clause.
    pub fn injectivity(activated_id: usize, activated_step: &ProofStep) -> Vec<ProofStep> {
        let clause = &activated_step.clause;
        let mut answer = vec![];

        for (index, arg, literals, flipped) in clause.find_injectivities() {
            let context = activated_step.clause.get_local_context().clone();
            let info = InjectivityInfo {
                id: activated_id,
                index,
                arg,
                literals: literals.clone(),
                context: context.clone(),
                flipped,
            };
            let (clause, traces) = Clause::normalize_with_trace(literals, &context);
            let step = ProofStep::direct(
                activated_id,
                activated_step,
                Rule::Injectivity(info),
                clause,
                traces,
            );
            answer.push(step);
        }

        answer
    }

    /// Apply boolean reduction to derive new clauses.
    pub fn boolean_reduction(
        &self,
        activated_id: usize,
        activated_step: &ProofStep,
        kernel_context: &KernelContext,
    ) -> Vec<ProofStep> {
        let clause = &activated_step.clause;
        let mut answer = vec![];

        for (index, literals) in clause.find_boolean_reductions(kernel_context) {
            let context = activated_step.clause.get_local_context().clone();
            let info = BooleanReductionInfo {
                id: activated_id,
                index,
                literals: literals.clone(),
                context: context.clone(),
            };
            let (clause, traces) = Clause::normalize_with_trace(literals, &context);
            let step = ProofStep::direct(
                activated_id,
                activated_step,
                Rule::BooleanReduction(info),
                clause,
                traces,
            );
            answer.push(step);
        }

        answer
    }

    /// Apply extensionality to derive function equality from pointwise equality.
    /// When f(x1, x2, ...) = g(x1, x2, ...) for all arguments, that implies f = g.
    pub fn extensionality(
        &self,
        activated_id: usize,
        activated_step: &ProofStep,
        kernel_context: &KernelContext,
    ) -> Vec<ProofStep> {
        let clause = &activated_step.clause;
        let mut answer = vec![];

        if let Some(literals) = clause.find_extensionality(kernel_context) {
            let context = activated_step.clause.get_local_context().clone();
            let info = ExtensionalityInfo {
                id: activated_id,
                literals: literals.clone(),
                context: context.clone(),
            };
            let (clause, traces) = Clause::normalize_with_trace(literals, &context);
            let step = ProofStep::direct(
                activated_id,
                activated_step,
                Rule::Extensionality(info),
                clause,
                traces,
            );
            answer.push(step);
        }

        answer
    }

    /// Tries to do inference using the equality factoring (EF) rule.
    ///
    /// Given:
    ///   s = t | u = v | R
    /// if we can unify s and u, we can rewrite it to:
    ///   t != v | u = v | R
    ///
    /// "s = t" must be the first clause, but "u = v" can be any of them.
    ///
    /// I find this rule to be unintuitive, extracting an inequality from only equalities.
    pub fn equality_factoring(
        activated_id: usize,
        activated_step: &ProofStep,
        kernel_context: &KernelContext,
    ) -> Vec<ProofStep> {
        let clause = &activated_step.clause;
        let mut answer = vec![];

        // Use the clause's helper method to find all factorings
        let factorings = inference::find_equality_factorings(clause, kernel_context);

        for (literals, ef_trace, output_context) in factorings {
            // Capture the literals before normalization
            let literals_before_normalization = literals.clone();

            // Create the new clause with trace using the unifier's output context
            let (new_clause, normalization_traces) =
                Clause::normalize_with_trace(literals, &output_context);

            let step = ProofStep::direct(
                activated_id,
                activated_step,
                Rule::EqualityFactoring(EqualityFactoringInfo {
                    id: activated_id,
                    literals: literals_before_normalization,
                    context: output_context,
                    ef_trace,
                }),
                new_clause,
                normalization_traces,
            );
            answer.push(step);
        }

        answer
    }

    pub fn get_clause(&self, index: usize) -> &Clause {
        &self.steps[index].clause
    }

    pub fn has_step(&self, index: usize) -> bool {
        index < self.steps.len()
    }

    pub fn get_step(&self, index: usize) -> &ProofStep {
        &self.steps[index]
    }

    /// Iterate over all active proof steps.
    pub fn iter_steps(&self) -> impl Iterator<Item = (usize, &ProofStep)> {
        self.steps.iter().enumerate()
    }

    /// Iterate over all proof steps that depend on this id.
    pub fn find_consequences(&self, id: usize) -> impl Iterator<Item = (usize, &ProofStep)> {
        self.steps
            .iter()
            .enumerate()
            .filter(move |(_, step)| step.depends_on_active(id))
    }

    /// Returns (value, trace) when this literal's value is known due to some existing clause.
    /// The trace is either Eliminated, if the literal matched an existing one, or Impossible,
    /// if the literal is self-evident.
    fn evaluate_literal(
        &self,
        literal: &Literal,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<(bool, LiteralTrace)> {
        literal.validate_type(local_context, kernel_context);
        if literal.left == literal.right {
            return Some((literal.positive, LiteralTrace::Impossible));
        }
        match self
            .literal_set
            .find_generalization(&literal, local_context, kernel_context)
        {
            Some((positive, step, flipped)) => {
                Some((positive, LiteralTrace::Eliminated { step, flipped }))
            }
            None => None,
        }
    }

    /// Simplifies the clause based on both structural rules and the active set.
    /// If the result is redundant given what's already known, return None.
    /// Specializations are allowed, though, even if they're redundant.
    /// If the result is an impossibility, return an empty clause.
    pub fn simplify(
        &self,
        mut step: ProofStep,
        kernel_context: &KernelContext,
    ) -> Option<ProofStep> {
        if step.clause.is_tautology() {
            return None;
        }

        if self.is_known_long_clause(&step.clause) {
            return None;
        }

        // Filter out any literals that are known to be true
        let mut new_rules = vec![];
        let initial_num_literals = step.clause.literals.len();
        let mut output_literals = vec![];
        let mut incremental_trace = vec![];
        let local_context = step.clause.get_local_context().clone();
        for literal in std::mem::take(&mut step.clause.literals) {
            match self.evaluate_literal(&literal, &local_context, kernel_context) {
                Some((true, _)) => {
                    // This literal is already known to be true.
                    // Thus, the whole clause is a tautology.
                    return None;
                }
                Some((false, trace)) => {
                    // This literal is already known to be false.
                    // Thus, we can just omit it from the disjunction.
                    if let Some(id) = trace.step_id() {
                        new_rules.push((id, self.get_step(id)));
                    }
                    incremental_trace.push(trace);
                    continue;
                }
                None => {
                    let output_index = output_literals.len();
                    output_literals.push(literal);
                    incremental_trace.push(LiteralTrace::Output {
                        index: output_index,
                        flipped: false,
                    });
                }
            }
        }

        if output_literals.len() == initial_num_literals {
            // This proof step hasn't changed.
            step.clause.literals = output_literals;
            return Some(step);
        }

        let (clause, trace) = Clause::new_composing_traces(
            output_literals,
            step.trace.clone(),
            &ClauseTrace::new(incremental_trace),
            step.clause.get_local_context(),
        );
        if clause.is_tautology() {
            return None;
        }
        if self.is_known_long_clause(&clause) {
            return None;
        }
        Some(ProofStep::simplified(step, &new_rules, clause, trace))
    }

    fn add_resolution_targets(
        &mut self,
        step_index: usize,
        literal_index: usize,
        literal: &Literal,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        let tree = if literal.positive {
            &mut self.positive_res_targets
        } else {
            &mut self.negative_res_targets
        };
        tree.insert(
            &literal.left,
            ResolutionTarget {
                step_index,
                literal_index,
                left: true,
            },
            local_context,
            kernel_context,
        );
        tree.insert(
            &literal.right,
            ResolutionTarget {
                step_index,
                literal_index,
                left: false,
            },
            local_context,
            kernel_context,
        );
    }

    /// Indexes a clause so that it becomes available for future proof step generation.
    /// Return its id.
    fn insert(&mut self, step: ProofStep, kernel_context: &KernelContext) -> usize {
        let step_index = self.next_id();
        let clause = &step.clause;
        let local_context = clause.get_local_context();

        // Add resolution targets for the new clause.
        for (i, literal) in clause.literals.iter().enumerate() {
            self.add_resolution_targets(step_index, i, literal, local_context, kernel_context);
        }

        // Store long clauses here. Short clauses will be kept in the literal set.
        if clause.literals.len() > 1 {
            self.long_clauses.insert(clause.clone());
        }

        self.steps.push(step);
        step_index
    }

    pub fn next_id(&self) -> usize {
        self.steps.len()
    }

    // term1 and term2 are specializations of pattern_id.
    // If forwards, the pattern is term1 = term2. Otherwise, it is term2 = term1.
    fn add_to_term_graph(
        &mut self,
        pattern_id: usize,
        inspiration_id: Option<usize>,
        term1: TermId,
        term2: TermId,
        forwards: bool,
        equal: bool,
    ) {
        let (left, right) = if forwards {
            (term1, term2)
        } else {
            (term2, term1)
        };
        if equal {
            self.graph
                .set_terms_equal(left, right, StepId(pattern_id), inspiration_id.map(StepId));
        } else {
            assert!(inspiration_id.is_none());
            self.graph
                .set_terms_not_equal(left, right, StepId(pattern_id));
        }
    }

    /// Inference that is specific to literals.
    fn activate_literal(
        &mut self,
        activated_step: &ProofStep,
        output: &mut Vec<ProofStep>,
        kernel_context: &KernelContext,
    ) {
        let activated_id = self.next_id();
        assert_eq!(activated_step.clause.len(), 1);
        let literal = &activated_step.clause.literals[0];

        // Using the literal as a rewrite target.
        if !literal.has_any_variable() {
            // Add this to the term graph.
            let left = self.graph.insert_term(&literal.left, kernel_context);
            let right = self.graph.insert_term(&literal.right, kernel_context);

            self.add_to_term_graph(activated_id, None, left, right, true, literal.positive);

            // The activated step could be rewritten immediately.
            self.activate_rewrite_target(activated_id, &activated_step, output, kernel_context);
        }

        // Using the literal as a rewrite pattern.
        if literal.positive && !activated_step.rule.is_rewrite() {
            // The activated step could be used as a rewrite pattern immediately.
            self.activate_rewrite_pattern(activated_id, &activated_step, output, kernel_context);

            // Index it so that it can be used as a rewrite pattern in the future.
            self.rewrite_tree.insert_literal(
                activated_id,
                literal,
                activated_step.clause.get_local_context(),
                kernel_context,
            );
        }

        self.literal_set.insert(
            &literal,
            activated_id,
            activated_step.clause.get_local_context(),
            kernel_context,
        );
    }

    /// Generate all the inferences that can be made from a given clause, plus some existing clause.
    /// This function does not simplify the inferences, or use the inferences to simplify anything else.
    /// The prover will do all forms of simplification separately.
    /// After generation, this clause is added to the active set.
    /// Returns the id of the new clause, and pairs describing how the generated clauses were proved.
    pub fn activate(
        &mut self,
        activated_step: ProofStep,
        kernel_context: &KernelContext,
    ) -> (usize, Vec<ProofStep>) {
        let mut output = vec![];
        let activated_id = self.next_id();

        // Unification-based inferences don't need to be done on specialization, because
        // they can operate directly on the general form.
        for proof_step in
            ActiveSet::equality_resolution(activated_id, &activated_step, kernel_context)
        {
            output.push(proof_step);
        }

        for proof_step in
            ActiveSet::equality_factoring(activated_id, &activated_step, kernel_context)
        {
            output.push(proof_step);
        }

        for proof_step in ActiveSet::injectivity(activated_id, &activated_step) {
            output.push(proof_step);
        }

        for proof_step in self.boolean_reduction(activated_id, &activated_step, kernel_context) {
            output.push(proof_step);
        }

        for proof_step in self.extensionality(activated_id, &activated_step, kernel_context) {
            output.push(proof_step);
        }

        self.find_resolutions(&activated_step, &mut output, kernel_context);

        if activated_step.clause.len() == 1 {
            self.activate_literal(&activated_step, &mut output, kernel_context);
        }

        self.insert(activated_step, kernel_context);
        (activated_id, output)
    }

    pub fn iter_clauses(&self) -> impl Iterator<Item = &Clause> {
        self.steps.iter().map(|step| &step.clause)
    }

    /// Find the index of all clauses used to prove the provided step.
    pub fn find_upstream(
        &self,
        step: &ProofStep,
        include_inspiration: bool,
        output: &mut HashSet<usize>,
    ) {
        let mut pending = vec![];
        for i in step.active_dependencies(include_inspiration) {
            pending.push(i);
        }
        while !pending.is_empty() {
            let i = pending.pop().unwrap();
            if output.contains(&i) {
                continue;
            }
            output.insert(i);
            for j in self.get_step(i).active_dependencies(include_inspiration) {
                pending.push(j);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_activate_rewrite_pattern() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constants(&["c1", "c2", "c3", "c4"], "Bool");

        // Create an active set that knows g0(c3, c4) = c2
        let mut set = ActiveSet::new();
        let clause = kctx.parse_clause("g0(c3, c4) = c2", &[]);
        let mut step = ProofStep::mock_from_clause(clause);
        step.truthiness = Truthiness::Hypothetical;
        set.activate(step, &kctx);

        // We should be able to replace c3 with c1 in "g0(c3, c4) = c2"
        let pattern_clause = kctx.parse_clause("c1 = c3", &[]);
        let pattern_step = ProofStep::mock_from_clause(pattern_clause);
        let mut result = vec![];
        set.activate_rewrite_pattern(1, &pattern_step, &mut result, &kctx);

        assert_eq!(result.len(), 1);
        let expected = kctx.parse_clause("g0(c1, c4) = c2", &[]);
        assert_eq!(result[0].clause, expected);
    }

    #[test]
    fn test_activate_rewrite_target() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constants(&["c1", "c2", "c3", "c4"], "Bool");

        // Create an active set that knows c1 = c3
        let mut set = ActiveSet::new();
        let clause = kctx.parse_clause("c1 = c3", &[]);
        set.activate(ProofStep::mock_from_clause(clause), &kctx);

        // We want to use g0(c3, c4) = c2 to get g0(c1, c4) = c2.
        let target_clause = kctx.parse_clause("g0(c3, c4) = c2", &[]);
        let mut target_step = ProofStep::mock_from_clause(target_clause);
        target_step.truthiness = Truthiness::Hypothetical;
        let mut result = vec![];
        set.activate_rewrite_target(1, &target_step, &mut result, &kctx);
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_equality_resolution() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1"], "Bool");

        // x0 != c0 or x0 = c1
        // When x0 unifies with itself, the first literal is eliminated and we get c1 = c0
        let clause = kctx.parse_clause("x0 != c0 or x0 = c1", &["Bool"]);
        let mock_step = ProofStep::mock_from_clause(clause);
        let proof_steps = ActiveSet::equality_resolution(0, &mock_step, &kctx);
        assert_eq!(proof_steps.len(), 1);
        assert!(proof_steps[0].clause.len() == 1);
        assert_eq!(format!("{}", proof_steps[0].clause), "c1 = c0".to_string());
    }

    #[test]
    fn test_mutually_recursive_equality_resolution() {
        // This is a bug we ran into. It shouldn't work
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constant("c0", "Bool");

        let clause = kctx.parse_clause(
            "g0(x0, g0(x1, g1(x2, c0))) != g0(g0(x2, x1), x0)",
            &["Bool", "Bool", "Bool"],
        );
        let mock_step = ProofStep::mock_from_clause(clause);
        assert!(ActiveSet::equality_resolution(0, &mock_step, &kctx).is_empty());
    }

    #[test]
    fn test_equality_factoring_basic() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool");

        // x0 = c0 or x1 = c0
        // Equality factoring gives us c0 = x0
        let clause = kctx.parse_clause("x0 = c0 or x1 = c0", &["Bool", "Bool"]);
        let mock_step = ProofStep::mock_from_clause(clause);
        let proof_steps = ActiveSet::equality_factoring(0, &mock_step, &kctx);
        let expected = kctx.parse_clause("c0 = x0", &["Bool"]);
        for ps in &proof_steps {
            if ps.clause == expected {
                return;
            }
        }
        panic!("Did not find expected clause");
    }

    #[test]
    fn test_matching_entire_literal() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constant("g2", "(Bool, Bool) -> Bool")
            .parse_constants(&["c3", "c4", "c5", "c6", "c7"], "Bool");

        let mut set = ActiveSet::new();
        // Test that we can match an entire literal against a rewrite rule.
        // Use g2(g0(g0(x0, c4), c5), c6) or g0(x0, c7) != x0
        // When we have g0(c3, c7) = c3, this should resolve to just not g2(...).
        let clause1 = kctx.parse_clause(
            "not g2(g0(g0(x0, c4), c5), c6) or g0(x0, c7) != x0",
            &["Bool"],
        );
        let mut step = ProofStep::mock_from_clause(clause1);
        step.truthiness = Truthiness::Factual;
        set.activate(step, &kctx);

        let clause2 = kctx.parse_clause("g0(c3, c7) = c3", &[]);
        let mut step = ProofStep::mock_from_clause(clause2);
        step.truthiness = Truthiness::Counterfactual;
        let (_, new_clauses) = set.activate(step, &kctx);

        // Find the expected clause in results
        let expected = "not g2(g0(g0(c3, c4), c5), c6)";
        assert!(
            new_clauses
                .iter()
                .any(|ps| ps.clause.to_string() == expected),
            "Expected clause '{}' not found in {:?}",
            expected,
            new_clauses
                .iter()
                .map(|ps| ps.clause.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_equality_factoring_variable_numbering() {
        // This is a bug we ran into
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g1", "(Bool, Bool) -> Bool");

        let mut set = ActiveSet::new();

        // Nonreflexive rule of less-than
        let clause1 = kctx.parse_clause("not g1(x0, x0)", &["Bool"]);
        set.activate(ProofStep::mock_from_clause(clause1), &kctx);

        // Trichotomy
        let clause2 = kctx.parse_clause("g1(x0, x1) or g1(x1, x0) or x0 = x1", &["Bool", "Bool"]);
        let mock_step = ProofStep::mock_from_clause(clause2);
        let output = ActiveSet::equality_factoring(0, &mock_step, &kctx);
        assert_eq!(output[0].clause.to_string(), "g1(x0, x0) or x0 = x0");
    }

    #[test]
    fn test_self_referential_resolution() {
        // This is a bug we ran into. These things should not unify
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constant("g2", "(Bool, Bool) -> Bool")
            .parse_constant("c0", "Bool");

        let mut set = ActiveSet::new();
        let clause1 = kctx.parse_clause("g2(x0, x0) = c0", &["Bool"]);
        set.activate(ProofStep::mock_from_clause(clause1), &kctx);

        let clause2 = kctx.parse_clause(
            "g2(g2(g1(c0, x0), x0), g2(x1, x1)) != c0",
            &["Bool", "Bool"],
        );
        let mut step = ProofStep::mock_from_clause(clause2);
        step.truthiness = Truthiness::Counterfactual;
        let mut results = vec![];
        set.find_resolutions(&step, &mut results, &kctx);
        assert_eq!(results.len(), 0);
    }

    /// Test that polymorphic rewriting produces well-typed clauses.
    /// This tests a bug where backwards rewriting a concrete term with a polymorphic pattern
    /// produces a clause where the left and right sides have mismatched types.
    ///
    /// BUG: This test currently fails because the rewrite tree produces ill-typed literals
    /// when backwards rewriting with polymorphic patterns. The rewrite substitutes type
    /// variables (like x0, x1) into positions that expect ground types, resulting in
    /// type mismatches like `g1(g1(Type, x0, ...), T1, ...) = c1` where the left side
    /// has type involving FreeVariables but c1 has a ground type.
    #[test]
    fn test_polymorphic_backwards_rewrite_type_consistency() {
        let mut kctx = KernelContext::new();
        // Use names that don't start with 'T' to avoid collision with type variable syntax
        kctx.parse_datatype("Foo");
        kctx.parse_datatype("Bar");
        // Pair is a parameterized type: Pair[T, U]
        kctx.parse_type_constructor("Pair", 2);

        // g0 = Pair.new: (T: Type) -> (U: Type) -> T -> U -> Pair[T, U]
        kctx.parse_polymorphic_constant("g0", "T: Type, U: Type", "T -> U -> Pair[T, U]");
        // g1 = Pair.first: (T: Type) -> (U: Type) -> Pair[T, U] -> T
        kctx.parse_polymorphic_constant("g1", "T: Type, U: Type", "Pair[T, U] -> T");
        // g2 = Pair.second: (T: Type) -> (U: Type) -> Pair[T, U] -> U
        kctx.parse_polymorphic_constant("g2", "T: Type, U: Type", "Pair[T, U] -> U");
        kctx.parse_constant("c1", "Foo");
        kctx.parse_constant("c2", "Bar");

        let mut set = ActiveSet::new();

        // Add the polymorphic axiom for first: g1(x0, x1, g0(x0, x1, x2, x3)) = x2
        // This is: Pair.first(T, U, Pair.new(T, U, t, u)) = t
        // Context: x0: Type, x1: Type, x2: x0, x3: x1
        let first_axiom = kctx.parse_clause(
            "g1(x0, x1, g0(x0, x1, x2, x3)) = x2",
            &["Type", "Type", "x0", "x1"],
        );
        let mut first_step = ProofStep::mock_from_clause(first_axiom);
        first_step.truthiness = Truthiness::Factual;
        set.activate(first_step, &kctx);

        // Add the polymorphic axiom for second: g2(x0, x1, g0(x0, x1, x2, x3)) = x3
        // This is: Pair.second(T, U, Pair.new(T, U, t, u)) = u
        let second_axiom = kctx.parse_clause(
            "g2(x0, x1, g0(x0, x1, x2, x3)) = x3",
            &["Type", "Type", "x0", "x1"],
        );
        let mut second_step = ProofStep::mock_from_clause(second_axiom);
        second_step.truthiness = Truthiness::Factual;
        set.activate(second_step, &kctx);

        // Now activate a concrete target: Pair.first(Foo, Bar, Pair.new(Foo, Bar, c1, c2)) = c1
        // This triggers backwards rewriting which produces ill-typed clauses
        let target_clause = kctx.parse_clause("g1(Foo, Bar, g0(Foo, Bar, c1, c2)) = c1", &[]);
        let mut target_step = ProofStep::mock_from_clause(target_clause);
        target_step.truthiness = Truthiness::Counterfactual;

        // Use full activate which also does simplification
        let (_, result) = set.activate(target_step, &kctx);

        // Validate all generated clauses - this will catch type mismatches
        for ps in &result {
            ps.clause.validate(&kctx);
        }
    }
}
