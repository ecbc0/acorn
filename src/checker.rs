use std::borrow::Cow;
use std::collections::HashSet;
use std::sync::Arc;

use crate::certificate::Certificate;
use crate::code_generator::Error;
use crate::elaborator::acorn_type::AcornType;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::evaluator::Evaluator;
use crate::elaborator::names::ConstantName;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::source::Source;
use crate::elaborator::stack::Stack;
use crate::kernel::clause::Clause;
use crate::kernel::generalization_set::GeneralizationSet;
use crate::kernel::inference;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::{StepId, TermGraph};
use crate::normalizer::{Normalizer, NormalizerView};
use crate::project::Project;
use crate::syntax::expression::Declaration;
use crate::syntax::statement::{Statement, StatementInfo};
use tracing::trace;

/// The reason why a certificate step was accepted.
#[derive(Debug, Clone)]
pub enum StepReason {
    /// Proven by the term graph (concrete reasoning via congruence closure and propositional logic).
    TermGraph,

    /// An assumption based on normalizing a statement elsewhere in the code.
    /// The source points to the location of the assumption.
    Assumption(Source),

    /// A let...satisfy statement that skolemizes an exists statement.
    /// The source points to where the exists was originally defined.
    Skolemization(Source),

    /// A let...satisfy statement that introduces a synthetic definition.
    SyntheticDefinition,

    /// The checker already had a contradiction, so everything is trivially true.
    Contradiction,

    /// A claim statement from a previous certificate step.
    PreviousClaim,

    /// A clause inserted during testing.
    Testing,

    /// Proven by a single step of equality resolution, based on the given step id
    EqualityResolution(usize),

    /// Proven by extensionality, based on the given step id
    Extensionality(usize),

    /// Proven by equality factoring, based on the given step id
    EqualityFactoring(usize),

    /// Proven by injectivity, based on the given step id
    Injectivity(usize),

    /// Proven by boolean reduction, based on the given step id
    BooleanReduction(usize),
}

impl StepReason {
    pub fn description(&self) -> String {
        match self {
            StepReason::TermGraph => "simplification".to_string(),
            StepReason::Assumption(source) | StepReason::Skolemization(source) => {
                source.description()
            }
            StepReason::SyntheticDefinition => "synthetic definition".to_string(),
            StepReason::Contradiction => "ex falso".to_string(),
            StepReason::PreviousClaim => "previous claim".to_string(),
            StepReason::Testing => "testing".to_string(),
            StepReason::EqualityResolution(_) => "equality resolution".to_string(),
            StepReason::Extensionality(_) => "extensionality".to_string(),
            StepReason::EqualityFactoring(_) => "equality factoring".to_string(),
            StepReason::Injectivity(_) => "injectivity".to_string(),
            StepReason::BooleanReduction(_) => "boolean reduction".to_string(),
        }
    }

    pub fn dependency(&self) -> Option<usize> {
        match self {
            StepReason::EqualityResolution(step_id)
            | StepReason::Extensionality(step_id)
            | StepReason::EqualityFactoring(step_id)
            | StepReason::Injectivity(step_id)
            | StepReason::BooleanReduction(step_id) => Some(*step_id),
            _ => None,
        }
    }
}

/// Converts a clause to readable code using the environment's names.
fn clause_to_code(clause: &Clause, normalizer: &Normalizer, bindings: &Cow<BindingMap>) -> String {
    let value = normalizer.denormalize(clause, None);
    let mut code_gen = crate::code_generator::CodeGenerator::new(bindings);
    code_gen
        .value_to_code(&value)
        .unwrap_or_else(|_| format!("{} (internal)", clause))
}

/// Information about a single step in a certificate proof.
#[derive(Debug, Clone)]
pub struct CertificateStep {
    /// The statement from the certificate (the code line).
    pub statement: String,

    /// The reason this step was accepted.
    pub reason: StepReason,
}

/// The checker quickly checks if a clause can be proven in a single step from known clauses.
///
/// The types of single-step we support are:
///
///   Exact substitutions into a known theorem. Handled by the GeneralizationSet.
///   "Congruence closure" of equalities and subterm relationships. Handled by the TermGraph.
///   Propositional calculus on concrete literals. Handled by the TermGraph.
///   Introducing variables for existential quantifiers. Handled weirdly through a Normalizer.
#[derive(Clone)]
pub struct Checker {
    /// For deductions among concrete clauses.
    term_graph: TermGraph,

    /// For looking up specializations of clauses with free variables.
    generalization_set: Arc<GeneralizationSet>,

    /// Whether a contradiction was directly inserted into the checker.
    direct_contradiction: bool,

    /// A hack, but we need to break out of loops, since equality factoring and boolean
    /// reduction can create cycles.
    past_boolean_reductions: HashSet<Clause>,

    /// The reason for each step. The step_id is the index in this vector.
    reasons: Vec<StepReason>,
}

impl Checker {
    pub fn new() -> Checker {
        Checker {
            term_graph: TermGraph::new(),
            generalization_set: Arc::new(GeneralizationSet::new()),
            direct_contradiction: false,
            past_boolean_reductions: HashSet::new(),
            reasons: Vec::new(),
        }
    }

    /// Adds a true clause to the checker with a specific reason.
    pub fn insert_clause(
        &mut self,
        clause: &Clause,
        reason: StepReason,
        kernel_context: &KernelContext,
    ) {
        trace!(clause = %clause, reason = ?reason.description(), "inserting clause");

        if clause.is_impossible() {
            self.direct_contradiction = true;
            return;
        }

        let step_id = self.reasons.len();
        self.reasons.push(reason.clone());

        if clause.has_any_variable() {
            // The clause has free variables, so it can be a generalization.
            Arc::make_mut(&mut self.generalization_set).insert(
                clause.clone(),
                step_id,
                kernel_context,
            );

            // We only need to do equality resolution for clauses with free variables,
            // because resolvable concrete literals would already have been simplified out.
            for resolution in inference::equality_resolutions(clause, kernel_context) {
                self.insert_clause(
                    &resolution,
                    StepReason::EqualityResolution(step_id),
                    kernel_context,
                );
            }

            if let Some(extensionality) = clause.find_extensionality(kernel_context) {
                let ext_clause = Clause::new(extensionality, clause.get_local_context());
                self.insert_clause(
                    &ext_clause,
                    StepReason::Extensionality(step_id),
                    kernel_context,
                );
            }
        } else {
            // The clause is concrete.
            self.term_graph
                .insert_clause(clause, StepId(step_id), kernel_context);
        }

        for factoring in
            inference::equality_factorings(clause, clause.get_local_context(), kernel_context)
        {
            self.insert_clause(
                &factoring,
                StepReason::EqualityFactoring(step_id),
                kernel_context,
            );
        }

        for injectivity in clause.injectivities() {
            self.insert_clause(
                &injectivity,
                StepReason::Injectivity(step_id),
                kernel_context,
            );
        }

        for boolean_reduction in clause.boolean_reductions(kernel_context) {
            // Guard against infinite loops
            if self.past_boolean_reductions.contains(&boolean_reduction) {
                continue;
            }
            self.past_boolean_reductions
                .insert(boolean_reduction.clone());
            self.insert_clause(
                &boolean_reduction,
                StepReason::BooleanReduction(step_id),
                kernel_context,
            );
        }
    }

    /// Checks if a clause is known to be true, and returns the reason if so.
    /// Returns None if the clause cannot be proven.
    pub fn check_clause(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StepReason> {
        if self.has_contradiction() {
            trace!(clause = %clause, result = "contradiction", "checking clause");
            return Some(StepReason::Contradiction);
        }

        // Check the term graph for concrete evaluation
        if self.term_graph.check_clause(clause, kernel_context) {
            trace!(clause = %clause, result = "term_graph", "checking clause");
            return Some(StepReason::TermGraph);
        }

        // If not found in term graph, check if there's a generalization in the clause set
        if let Some(step_id) = self
            .generalization_set
            .find_generalization(clause.clone(), kernel_context)
        {
            trace!(clause = %clause, result = "generalization_set", "checking clause");
            return Some(self.reasons[step_id].clone());
        }

        trace!(clause = %clause, result = "failed", "checking clause");
        None
    }

    /// Returns true if the checker has encountered a contradiction.
    ///
    /// It is possible that both a clause and its negation are known to be true, and yet
    /// has_contradiction returns false.
    /// This is because we do not unify all terms we ever encounter.
    ///
    /// We do guarantee that if you insert both a term and its negation then
    /// has_contradiction will return true.
    pub fn has_contradiction(&self) -> bool {
        self.direct_contradiction || self.term_graph.has_contradiction()
    }

    /// Helper method to check a single line of code in a proof.
    pub fn check_code(
        &mut self,
        code: &str,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Cow<Normalizer>,
        certificate_steps: &mut Vec<CertificateStep>,
        kernel_context: &KernelContext,
    ) -> Result<(), Error> {
        // Parse as a statement with in_block=true to allow bare expressions
        let statement = Statement::parse_str_with_options(&code, true)?;

        // Create a new evaluator for this check
        let mut evaluator = Evaluator::new(project, bindings, None);

        match statement.statement {
            StatementInfo::VariableSatisfy(vss) => {
                // Create an exists value from the let...satisfy statement
                // The declarations become the existential quantifiers
                let mut decls = vec![];
                for decl in &vss.declarations {
                    match decl {
                        Declaration::Typed(name_token, type_expr) => {
                            let name = name_token.text().to_string();
                            let acorn_type = evaluator.evaluate_type(type_expr)?;
                            decls.push((name, acorn_type));
                        }
                        Declaration::SelfToken(_) => {
                            return Err(Error::GeneratedBadCode(
                                "Unexpected 'self' in let...satisfy statement".to_string(),
                            ));
                        }
                    }
                }

                // Bind the declared variables to the stack
                let mut stack = Stack::new();
                evaluator.bind_args(&mut stack, &vss.declarations, None)?;

                // Evaluate the condition with the declared variables on the stack
                let condition_value = evaluator.evaluate_value_with_stack(
                    &mut stack,
                    &vss.condition,
                    Some(&AcornType::Bool),
                )?;

                // Create an exists value and check if it matches any existing synthetic definition
                let types = decls.iter().map(|(_, ty)| ty.clone()).collect();
                let exists_value = AcornValue::exists(types, condition_value.clone());

                let (source, synthetic_atoms) =
                    match normalizer.to_mut().get_synthetic_definition(&exists_value) {
                        Some(def) => {
                            // Found an existing synthetic definition
                            (def.source.clone(), Some(def.atoms.clone()))
                        }
                        None => {
                            // No synthetic definition found
                            if condition_value != AcornValue::Bool(true) {
                                // Non-trivial condition must match a synthetic definition
                                return Err(Error::GeneratedBadCode(format!(
                                    "statement '{}' does not match any synthetic definition",
                                    code
                                )));
                            }
                            // Trivial case: no source or synthetic atoms
                            (None, None)
                        }
                    };

                // Add all the variables in decls to the bindings and the normalizer
                if let Some(atoms) = &synthetic_atoms {
                    // We have an existing synthetic definition, create aliases to it
                    for (i, (name, acorn_type)) in decls.iter().enumerate() {
                        let synthetic_id = atoms[i];
                        let synthetic_cname = ConstantName::Synthetic(synthetic_id);
                        // Non-generic: generic_type equals instance_type
                        let value = AcornValue::constant(
                            synthetic_cname.clone(),
                            vec![],
                            acorn_type.clone(),
                            acorn_type.clone(),
                            vec![],
                        );
                        let user_cname = ConstantName::unqualified(bindings.module_id(), name);
                        bindings.to_mut().add_constant_alias(
                            user_cname,
                            synthetic_cname,
                            PotentialValue::Resolved(value),
                            vec![],
                            None,
                        );
                    }
                } else {
                    // Trivial case, create new constants
                    for (name, acorn_type) in decls {
                        let cname = ConstantName::unqualified(bindings.module_id(), &name);
                        bindings.to_mut().add_unqualified_constant(
                            &name,
                            vec![],
                            acorn_type.clone(),
                            None,
                            None,
                            vec![],
                            None,
                            String::new(),
                        );
                        normalizer.to_mut().add_scoped_constant(cname, &acorn_type);
                    }
                }

                // Re-parse the expression with the newly defined variables and insert clauses
                // Only do this for non-trivial conditions (not Bool(true))
                if condition_value != AcornValue::Bool(true) {
                    let mut evaluator = Evaluator::new(project, bindings, None);
                    let value = evaluator.evaluate_value(&vss.condition, Some(&AcornType::Bool))?;

                    // The NormalizerView::Ref prevents us from accidentally mutating the normalizer here.
                    let mut view = NormalizerView::Ref(&normalizer);
                    let clauses = view.nice_value_to_clauses(&value, &mut vec![])?;
                    for clause in clauses {
                        self.insert_clause(
                            &clause,
                            StepReason::SyntheticDefinition,
                            kernel_context,
                        );
                    }
                }

                // Record this step
                let reason = match source {
                    Some(source) => StepReason::Skolemization(source),
                    None => StepReason::SyntheticDefinition,
                };
                certificate_steps.push(CertificateStep {
                    statement: code.to_string(),
                    reason,
                });

                Ok(())
            }
            StatementInfo::Claim(claim) => {
                let value = evaluator.evaluate_value(&claim.claim, Some(&AcornType::Bool))?;

                // We don't want to normalize these clauses because sometimes checking
                // only works on the non-normalized version.
                // So we use the denormalized clause.
                let mut view = NormalizerView::Ref(&normalizer);
                let clauses = view.value_to_denormalized_clauses(&value)?;

                // For multi-clause claims, we'll use the reason from the first clause that provides one.
                // This is unclear, but it's just informational for a rare case, so it's not too bad.
                let mut reason = None;
                let num_clauses = clauses.len();
                for mut clause in clauses {
                    match self.check_clause(&clause, kernel_context) {
                        Some(r) => {
                            if reason.is_none() {
                                reason = Some(r);
                            }
                        }
                        None => {
                            if num_clauses == 1 {
                                return Err(Error::GeneratedBadCode(format!(
                                    "Claim '{}' is not obviously true",
                                    code
                                )));
                            }

                            let clause_code = clause_to_code(&clause, normalizer, bindings);

                            return Err(Error::GeneratedBadCode(format!(
                                "In claim '{}', the clause '{}' is not obviously true",
                                code, clause_code
                            )));
                        }
                    }
                    clause.normalize();
                    self.insert_clause(&clause, StepReason::PreviousClaim, kernel_context);
                }

                // Record the certificate step with the reason we found
                if let Some(reason) = reason {
                    certificate_steps.push(CertificateStep {
                        statement: code.to_string(),
                        reason,
                    });
                }

                Ok(())
            }
            _ => {
                return Err(Error::GeneratedBadCode(format!(
                    "Expected a claim or let...satisfy statement, got: {}",
                    code
                )));
            }
        }
    }

    /// Insert goal clauses into the checker.
    /// Normalizes the goal and inserts all resulting clauses as assumptions.
    pub fn insert_goal(
        &mut self,
        goal: &crate::elaborator::goal::Goal,
        normalizer: &mut crate::normalizer::Normalizer,
    ) -> Result<(), Error> {
        trace!("checking {} (line {})", goal.name, goal.first_line);
        use crate::proof_step::Rule;

        let source = &goal.proposition.source;
        let (_, steps) = normalizer.normalize_goal(goal).map_err(|e| e.message)?;
        // Get kernel_context after normalizing, since normalize_goal may create new monomorphs
        let kernel_context = normalizer.kernel_context();
        for step in &steps {
            // Use the step's own source if it's an assumption (which includes negated goals),
            // otherwise use the goal's source
            let step_source = if let Rule::Assumption(info) = &step.rule {
                &info.source
            } else {
                source
            };
            self.insert_clause(
                &step.clause,
                StepReason::Assumption(step_source.clone()),
                kernel_context,
            );
        }
        Ok(())
    }

    /// Check a certificate. It is expected that the certificate has a proof.
    /// Returns a list of CertificateSteps showing how each step was verified.
    ///
    /// Consumes bindings, normalizer and the checker itself since they may be
    /// modified during checking and should not be reused afterwards.
    pub fn check_cert(
        mut self,
        cert: &Certificate,
        project: &Project,
        mut bindings: Cow<BindingMap>,
        mut normalizer: Cow<Normalizer>,
    ) -> Result<Vec<CertificateStep>, Error> {
        let Some(proof) = &cert.proof else {
            return Err(Error::NoProof);
        };

        let mut certificate_steps = Vec::new();

        for code in proof {
            if self.has_contradiction() {
                return Ok(certificate_steps);
            }
            let kernel_context = normalizer.kernel_context().clone();
            self.check_code(
                code,
                project,
                &mut bindings,
                &mut normalizer,
                &mut certificate_steps,
                &kernel_context,
            )?;
        }

        if self.has_contradiction() {
            Ok(certificate_steps)
        } else {
            Err(Error::GeneratedBadCode(
                "proof does not result in a contradiction".to_string(),
            ))
        }
    }

    /// Remove unneeded steps from the certificate.
    /// The certificate passed in should be valid.
    ///
    /// Consumes bindings, normalizer and the checker itself since they may be
    /// modified during checking and should not be reused afterwards.
    pub fn clean_cert(
        self,
        cert: Certificate,
        project: &Project,
        bindings: Cow<BindingMap>,
        normalizer: Cow<Normalizer>,
    ) -> Result<(Certificate, Vec<CertificateStep>), Error> {
        let mut good_cert = cert;
        let mut keep_count = 0;

        loop {
            let Some(proof) = &good_cert.proof else {
                return Err(Error::NoProof);
            };

            if keep_count >= proof.len() {
                // All steps are necessary, run final check
                let steps = self.check_cert(&good_cert, project, bindings, normalizer)?;
                return Ok((good_cert, steps));
            }

            // Try removing the step at index keep_count
            let mut test_cert = good_cert.clone();
            if let Some(test_proof) = &mut test_cert.proof {
                test_proof.remove(keep_count);
            }

            // Try checking with a fresh checker
            let c = self.clone();
            match c.check_cert(&test_cert, project, bindings.clone(), normalizer.clone()) {
                Ok(_) => {
                    good_cert = test_cert;
                }
                Err(_) => {
                    keep_count += 1;
                }
            }
        }
    }
}

/// A test wrapper that combines a Checker with a KernelContext.
#[cfg(test)]
struct TestChecker {
    checker: Checker,
    context: KernelContext,
}

#[cfg(test)]
impl TestChecker {
    /// Creates a TestChecker with properly typed symbols.
    fn with_clauses(clauses: &[&str]) -> TestChecker {
        let mut context = KernelContext::new();
        // c0-c5: Bool constants
        context.add_constants(&["c0", "c1", "c2", "c3", "c4", "c5"], "Bool");
        // m0, m1, m3, m4: (Bool, Bool) -> Bool functions
        context.add_constants(&["m0", "m1"], "(Bool, Bool) -> Bool");
        // m2 placeholder to get to m3 and m4
        context.add_constant("m2", "(Bool, Bool) -> Bool");
        context.add_constants(&["m3", "m4"], "(Bool, Bool) -> Bool");

        let mut checker = Checker::new();
        for clause_str in clauses {
            let clause = context.make_clause(clause_str, &[]);
            checker.insert_clause(&clause, StepReason::Testing, &context);
        }
        TestChecker { checker, context }
    }

    fn check_clause_str(&mut self, s: &str) {
        let clause = self.context.make_clause(s, &[]);
        if !self.checker.check_clause(&clause, &self.context).is_some() {
            panic!("check_clause_str(\"{}\") failed", s);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_checker_should_be_monovariant() {
        // This basic case works
        let mut checker1 = TestChecker::with_clauses(&[
            "not m0(m1(c5, c0), c1)",
            "m4(c4, m1(c5, c0)) != m1(c3, c0) or not m0(m1(c3, c0), c1) or m0(m1(c5, c0), c1) or c4 = c1",
        ]);

        checker1.check_clause_str(
            "m4(c4, m1(c5, c0)) != m1(c3, c0) or not m0(m1(c3, c0), c1) or c4 = c1",
        );

        // This is the basic case plus extra things. So it should also work.
        let mut checker2 = TestChecker::with_clauses(&[
            // The minimal set of clauses that screw up our result
            "m4(c4, c5) = c3",
            "c4 != c0",
            "m4(c4, c5) != c3 or m4(c4, m1(c5, c0)) = m1(c3, c0) or c4 = c0",

            // The clauses from the basic case
            "not m0(m1(c5, c0), c1)",
            "m4(c4, m1(c5, c0)) != m1(c3, c0) or not m0(m1(c3, c0), c1) or m0(m1(c5, c0), c1) or c4 = c1",
        ]);

        checker2.check_clause_str(
            "m4(c4, m1(c5, c0)) != m1(c3, c0) or not m0(m1(c3, c0), c1) or c4 = c1",
        );
    }

    #[test]
    fn test_checker_cascades_updates() {
        // "c0 or c1 or c2" should combine with "not c2" to yield "c0 or c1".
        // That should then reduce via truth table logic with "not c0 or c1" to yield "c1".
        let mut checker = TestChecker::with_clauses(&["c0 or c1 or c2", "not c0 or c1", "not c2"]);
        checker.check_clause_str("c1");
    }
}
