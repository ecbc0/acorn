use std::cmp::Ordering;
use std::fmt;

use crate::elaborator::source::{Source, SourceType};
use crate::kernel::atom::Atom;
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::{PathStep, Term};
use crate::kernel::trace::{ClauseTrace, LiteralTrace};

/// The different sorts of proof steps.
#[derive(Debug, Eq, PartialEq, Hash, Clone, Copy)]
pub enum ProofStepId {
    /// A proof step that was activated and exists in the active set.
    Active(usize),

    /// A proof step that was never activated, but was used to find a contradiction.
    Passive(u32),

    /// The final step of a proof.
    /// No active id because it never gets inserted into the active set.
    Final,
}

impl ProofStepId {
    pub fn active_id(&self) -> Option<usize> {
        match self {
            ProofStepId::Active(id) => Some(*id),
            _ => None,
        }
    }
}

/// The "truthiness" categorizes the different types of true statements, relative to a proof.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Truthiness {
    /// A "factual" truth is true globally, regardless of this particular proof.
    Factual,

    /// A "hypothetical" truth is something that we are assuming true in the context of this proof.
    /// For example, we might assume that a and b are nonzero, and then prove that a * b != 0.
    Hypothetical,

    /// When we want to prove a goal G, we tell the prover that !G is true, and search
    /// for contradictions.
    /// A "counterfactual" truth is this negated goal, or something derived from it, that we expect
    /// to lead to a contradiction.
    Counterfactual,
}

impl Truthiness {
    /// When combining truthinesses, the result is the "most untruthy" of the two.
    pub fn combine(&self, other: Truthiness) -> Truthiness {
        match (self, other) {
            (Truthiness::Counterfactual, _) => Truthiness::Counterfactual,
            (_, Truthiness::Counterfactual) => Truthiness::Counterfactual,
            (Truthiness::Hypothetical, _) => Truthiness::Hypothetical,
            (_, Truthiness::Hypothetical) => Truthiness::Hypothetical,
            (Truthiness::Factual, Truthiness::Factual) => Truthiness::Factual,
        }
    }
}

/// Information about a resolution inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolutionInfo {
    /// Which clauses were used as the sources.
    /// The short clause must have only one literal.
    pub short_id: usize,

    /// The long clause will usually have more than one literal. It can have just one literal
    /// if we're finding a contradiction.
    pub long_id: usize,
}

/// Information about a specialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecializationInfo {
    /// The specialization is taking the pattern and substituting in particular values.
    pub pattern_id: usize,

    /// The inspiration isn't mathematically necessary for the specialization to be true,
    /// but we used it to decide which substitutions to make.
    pub inspiration_id: usize,
}

/// Information about a rewrite inference.
/// Rewrites have two parts, the "pattern" that determines what gets rewritten into what,
/// and the "target" which contains the subterm that gets rewritten.
/// Both of these parts are single-literal clauses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteInfo {
    /// Which clauses were used as the sources.
    pub pattern_id: usize,
    pub target_id: usize,

    /// Whether we rewrite the term on the left of the target literal. (As opposed to the right.)
    pub target_left: bool,

    /// The path within the target term that we rewrite.
    /// Uses PathStep::Function/Argument to navigate the curried term structure.
    pub path: Vec<PathStep>,

    /// Whether this is a forwards or backwards rewrite.
    /// A forwards rewrite rewrites the left side of the pattern into the right.
    pub forwards: bool,

    /// The literal initially created by the rewrite.
    /// This is usually redundant, but not always, because the output clause can get simplified.
    pub rewritten: Literal,

    /// The variable context for the rewritten literal.
    /// This is needed because normalization may renumber variables, so the clause's
    /// context might not match the rewritten literal's variables.
    pub context: LocalContext,

    /// Whether the literal was flipped during normalization
    pub flipped: bool,
}

/// Information about a contradiction found by rewriting one side of an inequality into the other.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MultipleRewriteInfo {
    /// The id of the inequality clause.
    pub inequality_id: usize,
    /// The ids of active clauses used in the rewrite chain.
    pub active_ids: Vec<usize>,
    /// The ids of passive clauses used in the rewrite chain.
    pub passive_ids: Vec<u32>,
}

/// Information about an assumption.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssumptionInfo {
    /// The source of the assumption.
    pub source: Source,

    /// If this assumption is the definition of a particular atom, this is the atom.
    pub defined_atom: Option<Atom>,

    /// The literals of the assumption before any simplification.
    pub literals: Vec<Literal>,

    /// The local context for the literals (variable types).
    pub context: LocalContext,
}

/// Information about what happens to a term during equality factoring.
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct EFTermTrace {
    /// Which literal it goes to
    pub index: usize,

    /// Whether it goes to the left of that literal
    pub left: bool,
}

/// Information about what happens to a literal during equality factoring.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EFLiteralTrace {
    pub left: EFTermTrace,
    pub right: EFTermTrace,
}

impl EFLiteralTrace {
    pub fn to_index(index: usize, flipped: bool) -> EFLiteralTrace {
        EFLiteralTrace::to_out(
            EFTermTrace { index, left: true },
            EFTermTrace { index, left: false },
            flipped,
        )
    }

    /// Trace a literal that goes to a provided output. Flip the input if flipped is provided.
    pub fn to_out(left: EFTermTrace, right: EFTermTrace, flipped: bool) -> EFLiteralTrace {
        if flipped {
            EFLiteralTrace::new(right, left)
        } else {
            EFLiteralTrace::new(left, right)
        }
    }

    pub fn new(left: EFTermTrace, right: EFTermTrace) -> EFLiteralTrace {
        EFLiteralTrace { left, right }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EqualityFactoringInfo {
    /// The id of the clause that was factored.
    pub id: usize,

    /// The literals that we got immediately after factoring.
    pub literals: Vec<Literal>,

    /// The local context for the literals.
    pub context: LocalContext,

    /// Parallel to literals. Tracks how we got them from the input clause.
    pub ef_trace: Vec<EFLiteralTrace>,
}

/// Information about an equality resolution inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EqualityResolutionInfo {
    /// The id of the clause that was resolved.
    pub id: usize,

    // Which literal in the input clause got resolved away.
    pub index: usize,

    // The literals that we got immediately after resolution.
    pub literals: Vec<Literal>,

    // The local context for the literals.
    pub context: LocalContext,

    // Parallel to literals. Tracks whether they were flipped or not.
    pub flipped: Vec<bool>,
}

/// Information about an injectivity inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InjectivityInfo {
    /// The id of the clause that had injectivity applied.
    pub id: usize,

    /// The literal that was eliminated.
    pub index: usize,

    /// The literals that we got immediately after function elimination.
    pub literals: Vec<Literal>,

    /// The local context for the literals.
    pub context: LocalContext,

    /// Whether the function-eliminated literal was flipped.
    pub flipped: bool,

    /// The argument to the eliminated function that we kept.
    pub arg: usize,
}

/// Information about a boolean reduction inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BooleanReductionInfo {
    /// The id of the clause that had boolean reduction applied.
    pub id: usize,

    /// The literal that got expanded into two literals.
    pub index: usize,

    /// The literals that we got immediately after boolean reduction.
    pub literals: Vec<Literal>,

    /// The local context for the literals.
    pub context: LocalContext,
}

/// Information about an extensionality inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionalityInfo {
    /// The id of the clause that had extensionality applied.
    pub id: usize,

    /// The literals that we got immediately after applying extensionality.
    pub literals: Vec<Literal>,

    /// The local context for the literals.
    pub context: LocalContext,
}

/// The rules that can generate new clauses, along with the clause ids used to generate.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Rule {
    Assumption(AssumptionInfo),

    /// Rules based on multiple source clauses
    Resolution(ResolutionInfo),
    Rewrite(RewriteInfo),
    Specialization(SpecializationInfo),

    /// Rules with only one source clause
    EqualityFactoring(EqualityFactoringInfo),
    EqualityResolution(EqualityResolutionInfo),
    Injectivity(InjectivityInfo),
    BooleanReduction(BooleanReductionInfo),
    Extensionality(ExtensionalityInfo),

    /// A contradiction found by repeatedly rewriting identical terms.
    MultipleRewrite(MultipleRewriteInfo),

    /// A contradiction between a number of passive clauses.
    PassiveContradiction(u32),
}

impl Rule {
    /// The ids of the clauses that this rule mathematically depends on.
    pub fn premises(&self) -> Vec<ProofStepId> {
        match self {
            Rule::Assumption(_) => vec![],
            Rule::Resolution(info) => vec![
                ProofStepId::Active(info.short_id),
                ProofStepId::Active(info.long_id),
            ],
            Rule::Rewrite(info) => vec![
                ProofStepId::Active(info.pattern_id),
                ProofStepId::Active(info.target_id),
            ],
            Rule::EqualityFactoring(info) => vec![ProofStepId::Active(info.id)],
            Rule::EqualityResolution(info) => vec![ProofStepId::Active(info.id)],
            Rule::Injectivity(info) => vec![ProofStepId::Active(info.id)],
            Rule::BooleanReduction(info) => vec![ProofStepId::Active(info.id)],
            Rule::Extensionality(info) => vec![ProofStepId::Active(info.id)],
            Rule::Specialization(info) => vec![ProofStepId::Active(info.pattern_id)],
            Rule::MultipleRewrite(multi_rewrite_info) => {
                let mut answer = vec![ProofStepId::Active(multi_rewrite_info.inequality_id)];
                for id in &multi_rewrite_info.active_ids {
                    answer.push(ProofStepId::Active(*id));
                }
                for id in &multi_rewrite_info.passive_ids {
                    answer.push(ProofStepId::Passive(*id));
                }
                answer
            }
            Rule::PassiveContradiction(n) => (0..*n).map(|id| ProofStepId::Passive(id)).collect(),
        }
    }

    /// Returns a human-readable name for this rule.
    pub fn name(&self) -> &str {
        match self {
            Rule::Assumption(_) => "Assumption",
            Rule::Resolution(_) => "Resolution",
            Rule::Rewrite(_) => "Rewrite",
            Rule::EqualityFactoring(_) => "Equality Factoring",
            Rule::EqualityResolution(_) => "Equality Resolution",
            Rule::Injectivity(_) => "Injectivity",
            Rule::BooleanReduction(_) => "Boolean Reduction",
            Rule::Extensionality(_) => "Extensionality",
            Rule::Specialization(_) => "Specialization",
            Rule::MultipleRewrite(..) => "Multiple Rewrite",
            Rule::PassiveContradiction(..) => "Passive Contradiction",
        }
    }

    pub fn is_rewrite(&self) -> bool {
        matches!(self, Rule::Rewrite(_))
    }

    pub fn is_assumption(&self) -> bool {
        matches!(self, Rule::Assumption(_))
    }

    pub fn is_negated_goal(&self) -> bool {
        match self {
            Rule::Assumption(info) => matches!(info.source.source_type, SourceType::NegatedGoal),
            _ => false,
        }
    }
}

/// A proof is made up of ProofSteps.
/// Each ProofStep contains an output clause, plus a bunch of information we track about it.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ProofStep {
    /// The proof step is primarily defined by a clause that it proves.
    /// Semantically, this clause is implied by the input clauses (activated and existing).
    pub clause: Clause,

    /// Whether this clause is the normal sort of true, or just something we're hypothesizing for
    /// the sake of the proof.
    pub truthiness: Truthiness,

    /// How this clause was generated.
    pub rule: Rule,

    /// Clauses that we used for additional simplification.
    pub simplification_rules: Vec<usize>,

    /// The number of proof steps that this proof step depends on.
    /// The size includes this proof step itself, but does not count assumptions and definitions.
    /// So the size for any assumption or definition is zero.
    /// This does not deduplicate among different branches, so it may be an overestimate.
    pub proof_size: u32,

    /// Not every proof step counts toward depth.
    /// When we use a new long clause to resolve against, that counts toward depth, because
    /// it roughly corresponds to "using a theorem".
    /// When we use a rewrite backwards, increasing KBO, that also counts toward depth.
    pub depth: u32,

    /// A printable proof step is one that we are willing to turn into a line of code in a proof.
    /// Unprintable proof steps are things like halfway resolved theorems, or expressions
    /// that use anonymous synthetic atoms.

    /// Information about this step that will let us reconstruct the variable mappings.
    pub trace: Option<ClauseTrace>,
}

impl fmt::Display for ProofStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ; rule = {:?}", self.clause, self.rule)
    }
}

impl ProofStep {
    /// Construct a new assumption ProofStep that is not dependent on any other steps.
    /// Assumptions are always depth zero, but eventually we may have to revisit that.
    pub fn assumption(source: &Source, clause: Clause, defined_atom: Option<Atom>) -> ProofStep {
        let source = source.clone();
        let truthiness = source.truthiness();
        let literals = clause.literals.clone();
        let context = clause.get_local_context().clone();
        let rule = Rule::Assumption(AssumptionInfo {
            source,
            defined_atom,
            literals,
            context,
        });

        // Create traces to indicate that no literals have been moved around
        let trace = Some(ClauseTrace::new(
            clause
                .literals
                .iter()
                .enumerate()
                .map(|(i, _)| LiteralTrace::Output {
                    index: i,
                    flipped: false,
                })
                .collect(),
        ));

        ProofStep {
            clause,
            truthiness,
            rule,
            simplification_rules: vec![],
            proof_size: 0,
            depth: 0,
            trace,
        }
    }

    /// Construct a new ProofStep that is a direct implication of a single activated step,
    /// not requiring any other clauses.
    pub fn direct(
        _activated_id: usize,
        activated_step: &ProofStep,
        rule: Rule,
        clause: Clause,
        trace: ClauseTrace,
    ) -> ProofStep {
        // Direct implication does not add to depth.
        let depth = activated_step.depth;

        ProofStep {
            clause,
            truthiness: activated_step.truthiness,
            rule,
            simplification_rules: vec![],
            proof_size: activated_step.proof_size + 1,
            depth,
            trace: Some(trace),
        }
    }

    /// Construct a ProofStep that is a specialization of a general pattern.
    pub fn specialization(
        pattern_id: usize,
        inspiration_id: usize,
        pattern_step: &ProofStep,
        clause: Clause,
        trace: ClauseTrace,
    ) -> ProofStep {
        let info = SpecializationInfo {
            pattern_id,
            inspiration_id,
        };
        ProofStep {
            clause,
            truthiness: pattern_step.truthiness,
            rule: Rule::Specialization(info),
            simplification_rules: vec![],
            proof_size: pattern_step.proof_size + 1,
            depth: pattern_step.depth,
            trace: Some(trace),
        }
    }

    /// Construct a new ProofStep via resolution.
    pub fn resolution(
        long_id: usize,
        long_step: &ProofStep,
        short_id: usize,
        short_step: &ProofStep,
        clause: Clause,
    ) -> ProofStep {
        let rule = Rule::Resolution(ResolutionInfo { short_id, long_id });

        let truthiness = short_step.truthiness.combine(long_step.truthiness);
        let proof_size = short_step.proof_size + long_step.proof_size + 1;

        let depth = if long_step.depth <= short_step.depth {
            if long_step.clause.contains(&clause) {
                // This is just a simplification
                short_step.depth
            } else {
                // This resolution is a new "theorem" that we are using.
                // So we need to add one to depth.
                short_step.depth + 1
            }
        } else {
            // This resolution is essentially continuing to resolve a theorem
            // statement that we have already fetched.
            long_step.depth
        };

        ProofStep {
            clause,
            truthiness,
            rule,
            simplification_rules: vec![],
            proof_size,
            depth,
            trace: None,
        }
    }

    /// Create a replacement for this clause that has extra simplification rules.
    /// The long step doesn't have an id because it isn't activated.
    pub fn simplified(
        long_step: ProofStep,
        short_steps: &[(usize, &ProofStep)],
        clause: Clause,
        trace: Option<ClauseTrace>,
    ) -> ProofStep {
        let mut truthiness = long_step.truthiness;
        let mut simplification_rules = long_step.simplification_rules;
        let mut proof_size = long_step.proof_size;
        let mut depth = long_step.depth;
        for (short_id, short_step) in short_steps {
            truthiness = truthiness.combine(short_step.truthiness);
            simplification_rules.push(*short_id);
            proof_size += short_step.proof_size;
            depth = u32::max(depth, short_step.depth);
        }

        ProofStep {
            clause,
            truthiness,
            rule: long_step.rule,
            simplification_rules,
            proof_size,
            depth,
            trace,
        }
    }

    /// Construct a new ProofStep via rewriting.
    /// We are replacing a subterm of the target literal with a new subterm.
    /// Note that the target step will always be a concrete single literal.
    /// The pattern and the output may have variables in them.
    /// It seems weird for the output to have variables, but it does.
    ///
    /// A "forwards" rewrite goes left-to-right in the pattern.
    ///
    /// The trace will capture everything that happens *after* the rewrite.
    pub fn rewrite(
        pattern_id: usize,
        pattern_step: &ProofStep,
        target_id: usize,
        target_step: &ProofStep,
        target_left: bool,
        path: &[PathStep],
        forwards: bool,
        new_subterm: &Term,
        new_subterm_context: &LocalContext,
    ) -> ProofStep {
        assert_eq!(target_step.clause.literals.len(), 1);

        let target_literal = &target_step.clause.literals[0];
        let (new_literal, flipped) =
            target_literal.replace_at_path(target_left, path, new_subterm.clone());
        let rewritten = new_literal.clone();

        let simplifying = new_literal.extended_kbo_cmp(&target_literal) == Ordering::Less;

        // Build the context from the rewritten literal.
        // Combine the target's context with the new_subterm's context.
        // The rewritten literal's variables come from both the target and the new_subterm.
        let rewritten_context = {
            let target_context = target_step.clause.get_local_context();
            let mut var_types = target_context.get_var_types().to_vec();
            let empty_type = Term::empty_type();
            for (i, vt) in new_subterm_context.get_var_types().iter().enumerate() {
                if i >= var_types.len() {
                    var_types.resize(i + 1, empty_type.clone());
                    var_types[i] = vt.clone();
                } else if var_types[i] == empty_type {
                    var_types[i] = vt.clone();
                }
            }
            LocalContext::from_types(var_types)
        };

        // Use rewritten_context for normalization since it has the correct variable types
        // for all variables in new_literal (from both target and new_subterm).
        let (clause, trace) = Clause::from_literal_traced(new_literal, false, &rewritten_context);

        let truthiness = pattern_step.truthiness.combine(target_step.truthiness);

        let rule = Rule::Rewrite(RewriteInfo {
            pattern_id,
            target_id,
            target_left,
            path: path.to_vec(),
            forwards,
            rewritten,
            context: rewritten_context,
            flipped,
        });

        let proof_size = pattern_step.proof_size + target_step.proof_size + 1;

        let dependency_depth = std::cmp::max(pattern_step.depth, target_step.depth);
        let depth = if simplifying {
            dependency_depth
        } else {
            dependency_depth + 1
        };

        ProofStep {
            clause,
            truthiness,
            rule,
            simplification_rules: vec![],
            proof_size,
            depth,
            trace: Some(trace),
        }
    }

    /// A proof step for finding a contradiction via a series of rewrites.
    pub fn multiple_rewrite(
        inequality_id: usize,
        active_ids: Vec<usize>,
        passive_ids: Vec<u32>,
        truthiness: Truthiness,
        depth: u32,
    ) -> ProofStep {
        let rule = Rule::MultipleRewrite(MultipleRewriteInfo {
            inequality_id,
            active_ids,
            passive_ids,
        });

        // proof size is wrong but we don't use it for a contradiction.
        ProofStep {
            clause: Clause::impossible(),
            truthiness,
            rule,
            simplification_rules: vec![],
            proof_size: 0,
            depth,
            trace: None,
        }
    }

    /// Assumes the provided steps are indexed by passive id, and that we use all of them.
    pub fn passive_contradiction(passive_steps: &[ProofStep]) -> ProofStep {
        let rule = Rule::PassiveContradiction(passive_steps.len() as u32);
        let mut truthiness = Truthiness::Factual;
        let mut depth = 0;
        let mut proof_size = 0;
        for step in passive_steps {
            truthiness = truthiness.combine(step.truthiness);
            depth = std::cmp::max(depth, step.depth);
            proof_size += step.proof_size;
        }

        ProofStep {
            clause: Clause::impossible(),
            truthiness,
            rule,
            simplification_rules: vec![],
            proof_size,
            depth,
            trace: None,
        }
    }

    /// Construct a ProofStep with fake heuristic data for testing/profiling.
    /// Uses an empty context (no variables).
    pub fn mock(s: &str, kernel: &KernelContext) -> ProofStep {
        use crate::kernel::clause::Clause;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;

        let local = LocalContext::empty();
        let literals: Vec<Literal> = s
            .split(" or ")
            .map(|part| Literal::parse(part.trim()))
            .collect();
        let clause = Clause::new(literals, &local);
        clause.validate(kernel);
        Self::mock_from_clause(clause)
    }

    /// Construct a ProofStep with properly typed terms for testing.
    /// var_types[i] is the type string for variable x_i.
    #[cfg(test)]
    pub fn mock_with_types(s: &str, var_types: &[&str], kernel: &KernelContext) -> ProofStep {
        let clause = kernel.make_clause(s, var_types);
        Self::mock_from_clause(clause)
    }

    pub fn mock_from_clause(clause: Clause) -> ProofStep {
        let truthiness = Truthiness::Factual;
        let literals = clause.literals.clone();
        let context = clause.get_local_context().clone();
        let rule = Rule::Assumption(AssumptionInfo {
            source: Source::mock(),
            defined_atom: None,
            literals,
            context,
        });
        ProofStep {
            clause,
            truthiness,
            rule,
            simplification_rules: vec![],
            proof_size: 0,
            depth: 0,
            trace: None,
        }
    }

    /// The ids of the other clauses that this clause depends on.
    pub fn dependencies(&self) -> Vec<ProofStepId> {
        let mut answer = self.rule.premises();
        for rule in &self.simplification_rules {
            answer.push(ProofStepId::Active(*rule));
        }
        answer
    }

    /// include_inspiration is whether we should include the inspiration clause in the dependencies.
    pub fn active_dependencies(&self, include_inspiration: bool) -> Vec<usize> {
        let mut answer: Vec<_> = self
            .dependencies()
            .iter()
            .filter_map(|id| match id {
                ProofStepId::Active(id) => Some(*id),
                _ => None,
            })
            .collect();
        if include_inspiration {
            if let Rule::Specialization(info) = &self.rule {
                answer.push(info.inspiration_id);
            }
        }
        answer
    }

    pub fn depends_on_active(&self, id: usize) -> bool {
        self.dependencies()
            .iter()
            .any(|i| *i == ProofStepId::Active(id))
    }

    /// Whether this is the last step of the proof
    pub fn finishes_proof(&self) -> bool {
        self.clause.is_impossible()
    }

    pub fn automatic_reject(&self) -> bool {
        // We have to strictly limit deduction that happens between two library facts, because
        // the plan is for the library to grow very large.
        if self.truthiness == Truthiness::Factual && self.proof_size > 2 {
            // Only do one step of deduction with global facts.
            return true;
        }

        // In some degenerate cases going very deep can crash the prover.
        if self.depth >= 30 {
            return true;
        }

        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::kernel_context::KernelContext;

    /// Test that the rewritten clause has correct variable types in its context.
    ///
    /// This tests a bug where ProofStep::rewrite used pattern_step's context for
    /// from_literal_traced, but the rewritten literal has variables from both the
    /// target and the new_subterm. This caused variable type lookups to fail
    /// because the pattern's context doesn't have types for variables from the target.
    ///
    /// The specific failure was:
    /// "failed to unify base literal ... with trace literal ..."
    /// because the clause's context didn't match the literal's variables.
    #[test]
    fn test_rewrite_clause_context_matches_variables() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("g0", "(Bool, Bool) -> Bool")
            .add_constant("g1", "Bool -> Bool")
            .add_constant("c0", "Bool");

        // Pattern: g0(x0, x1) = x1
        // Context: [Bool, Bool]
        let pattern_clause = kctx.make_clause("g0(x0, x1) = x1", &["Bool", "Bool"]);
        let pattern_context = pattern_clause.get_local_context().clone();
        let pattern_step = ProofStep::mock_from_clause(pattern_clause);

        // Target: g1(c0) = c0 (no variables)
        let target_clause = kctx.make_clause("g1(c0) = c0", &[]);
        let target_step = ProofStep::mock_from_clause(target_clause);

        // new_subterm: g0(x0, c0)
        // This introduces a variable x0 that's NOT in the pattern_step's context
        // (well, it is in this case, but in general it might have different types)
        let new_subterm = Term::parse("g0(x0, c0)");

        let rewrite_step = ProofStep::rewrite(
            0,
            &pattern_step,
            1,
            &target_step,
            true,  // target_left - replace g1(c0)
            &[],   // path - at root
            false, // forwards=false (backwards rewrite)
            &new_subterm,
            &pattern_context, // context for new_subterm's variables
        );

        // The clause should have all variables in its context
        // In this case, the rewritten literal is g0(x0, c0) = c0
        // which has variable x0
        let clause_context = rewrite_step.clause.get_local_context();
        for lit in &rewrite_step.clause.literals {
            for atom in lit.iter_atoms() {
                if let Atom::FreeVariable(var_id) = atom {
                    let var_type = clause_context.get_var_type(*var_id as usize);
                    assert!(
                        var_type.is_some(),
                        "Variable x{} in clause has no type in context (context len: {}). \
                         This indicates that from_literal_traced was called with the wrong context.",
                        var_id,
                        clause_context.len()
                    );
                }
            }
        }
    }
}
