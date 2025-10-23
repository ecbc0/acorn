use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::binding_map::BindingMap;
use crate::certificate::Certificate;
use crate::clause::Clause;
use crate::code_generator::Error;
use crate::evaluator::Evaluator;
use crate::expression::Declaration;
use crate::generalization_set::GeneralizationSet;
use crate::names::ConstantName;
use crate::normalizer::{Normalizer, NormalizerView};
use crate::potential_value::PotentialValue;
use crate::project::Project;
use crate::source::Source;
use crate::stack::Stack;
use crate::statement::{Statement, StatementInfo};
use crate::term_graph::{StepId, TermGraph};

/// The reason why a certificate step was accepted.
#[derive(Debug, Clone)]
pub enum StepReason {
    /// Proven by the term graph (concrete reasoning via congruence closure and propositional logic).
    TermGraph,

    /// Proven by specializing a general theorem or axiom from the environment.
    /// Contains the source information for where it was originally defined.
    Specialization(Source),

    /// A let...satisfy statement that skolemizes an exists statement.
    /// The source points to where the exists was originally defined.
    Skolemization(Source),

    /// A let...satisfy statement that introduces a synthetic definition.
    SyntheticDefinition,

    /// The checker already had a contradiction, so everything is trivially true.
    Contradiction,

    /// The reason is missing from our reason-tracking data structure.
    /// This indicates a bug, if we ever run into it.
    Missing,
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

    next_step_id: usize,

    /// Whether a contradiction was directly inserted into the checker.
    direct_contradiction: bool,

    /// Whether to track clause insertions in verbose mode.
    verbose: bool,

    /// Stringified versions of inserted clauses when verbose is true.
    insertions: Vec<String>,

    /// A hack, but we need to break out of loops, since equality factoring and boolean
    /// reduction can create cycles.
    past_boolean_reductions: HashSet<Clause>,

    /// Maps step_id to source for clauses that came from assumptions.
    /// Used to provide source info when a clause is proven via specialization.
    step_sources: HashMap<usize, Source>,
}

impl Checker {
    pub fn new() -> Self {
        Checker {
            term_graph: TermGraph::new(),
            generalization_set: Arc::new(GeneralizationSet::new()),
            next_step_id: 0,
            direct_contradiction: false,
            verbose: false,
            insertions: Vec::new(),
            past_boolean_reductions: HashSet::new(),
            step_sources: HashMap::new(),
        }
    }

    pub fn new_verbose() -> Self {
        let mut c = Checker::new();
        c.verbose = true;
        c
    }

    /// Adds a true clause to the checker.
    /// The source parameter indicates where this clause came from, if known.
    /// Single-source derived clauses (from equality resolution, etc.) inherit the same source.
    pub fn insert_clause(&mut self, clause: &Clause, source: Option<&Source>) {
        if self.verbose {
            self.insertions.push(clause.to_string());
        }

        if clause.is_impossible() {
            self.direct_contradiction = true;
            return;
        }

        let step_id = self.next_step_id;
        self.next_step_id += 1;

        // Track the source for this step, if we have one
        if let Some(source) = source {
            self.step_sources.insert(step_id, source.clone());
        }

        if clause.has_any_variable() {
            // The clause has free variables, so it can be a generalization.
            Arc::make_mut(&mut self.generalization_set).insert(clause.clone(), step_id);

            // We only need to do equality resolution for clauses with free variables,
            // because resolvable concrete literals would already have been simplified out.
            for resolution in clause.equality_resolutions() {
                self.insert_clause(&resolution, source);
            }

            if let Some(extensionality) = clause.find_extensionality() {
                let clause = Clause::new(extensionality);
                self.insert_clause(&clause, source);
            }
        } else {
            // The clause is concrete.

            // The term graph does all sorts of stuff but only for concrete clauses.
            self.term_graph.insert_clause(clause, StepId(step_id));
        }

        for factoring in clause.equality_factorings() {
            self.insert_clause(&factoring, source);
        }

        for injectivity in clause.injectivities() {
            self.insert_clause(&injectivity, source);
        }

        for boolean_reduction in clause.boolean_reductions() {
            if self.past_boolean_reductions.contains(&boolean_reduction) {
                continue;
            }
            self.past_boolean_reductions
                .insert(boolean_reduction.clone());
            self.insert_clause(&boolean_reduction, source);
        }
    }

    /// Checks if a clause is known to be true, and returns the reason if so.
    /// Returns None if the clause cannot be proven.
    pub fn check_clause(&mut self, clause: &Clause) -> Option<StepReason> {
        if self.has_contradiction() {
            return Some(StepReason::Contradiction);
        }

        // Check the term graph for concrete evaluation
        if self.term_graph.check_clause(clause) {
            return Some(StepReason::TermGraph);
        }

        // If not found in term graph, check if there's a generalization in the clause set
        if let Some(step_id) = self.generalization_set.find_generalization(clause.clone()) {
            // Look up the source for this step_id
            if let Some(source) = self.step_sources.get(&step_id).cloned() {
                return Some(StepReason::Specialization(source));
            } else {
                // We found a generalization but don't have source info for it.
                // This can happen for clauses that weren't assumptions from the environment.
                return Some(StepReason::Missing);
            }
        }

        if self.verbose {
            println!("With Checker::with_clauses(&[");
            for insertion in &self.insertions {
                println!("    \"{}\",", insertion);
            }
            println!("]);");
            println!("Failed check: \"{}\"", clause);
        }

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
    fn check_code(
        &mut self,
        code: &str,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Normalizer,
        certificate_steps: &mut Vec<CertificateStep>,
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
                    match normalizer.get_synthetic_definition(&exists_value) {
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
                        let value = AcornValue::constant(
                            synthetic_cname.clone(),
                            vec![],
                            acorn_type.clone(),
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
                            acorn_type,
                            None,
                            None,
                            vec![],
                            None,
                            String::new(),
                        );
                        normalizer.add_local_constant(cname);
                    }
                }

                // Re-parse the expression with the newly defined variables and insert clauses
                // Only do this for non-trivial conditions (not Bool(true))
                if condition_value != AcornValue::Bool(true) {
                    let mut evaluator = Evaluator::new(project, bindings, None);
                    let value = evaluator.evaluate_value(&vss.condition, Some(&AcornType::Bool))?;
                    let mut view = NormalizerView::Ref(&normalizer);
                    let clauses = view.nice_value_to_clauses(&value, &mut vec![])?;
                    for clause in clauses {
                        self.insert_clause(&clause, None);
                    }
                }

                // Record this step
                certificate_steps.push(CertificateStep {
                    statement: code.to_string(),
                    reason: match source {
                        Some(source) => StepReason::Skolemization(source),
                        None => StepReason::SyntheticDefinition,
                    },
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
                    match self.check_clause(&clause) {
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

                            // Convert the clause to readable code using the environment's names
                            let value = normalizer.denormalize(&clause, None);
                            let mut code_gen = crate::code_generator::CodeGenerator::new(bindings);
                            let clause_code = code_gen
                                .value_to_code(&value)
                                .unwrap_or_else(|_| format!("{} (internal)", clause));

                            return Err(Error::GeneratedBadCode(format!(
                                "In claim '{}', the clause '{}' is not obviously true",
                                code, clause_code
                            )));
                        }
                    }
                    clause.normalize();
                    self.insert_clause(&clause, None);
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

    /// Check a certificate. It is expected that the certificate has a proof.
    /// Returns a list of CertificateSteps showing how each step was verified.
    pub fn check_cert(
        &mut self,
        cert: &Certificate,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Normalizer,
    ) -> Result<Vec<CertificateStep>, Error> {
        let Some(proof) = &cert.proof else {
            return Err(Error::NoProof);
        };

        let mut certificate_steps = Vec::new();

        for code in proof {
            if self.has_contradiction() {
                return Ok(certificate_steps);
            }
            self.check_code(code, project, bindings, normalizer, &mut certificate_steps)?;
        }

        if self.has_contradiction() {
            Ok(certificate_steps)
        } else {
            Err(Error::GeneratedBadCode(
                "proof does not result in a contradiction".to_string(),
            ))
        }
    }

    #[cfg(test)]
    pub fn with_clauses(clauses: &[&str]) -> Checker {
        let mut checker = Checker::new();
        for clause_str in clauses {
            let clause = Clause::parse(clause_str);
            checker.insert_clause(&clause, None);
        }
        checker
    }

    #[cfg(test)]
    pub fn check_clause_str(&mut self, s: &str) {
        let clause = Clause::parse(s);
        if !self.check_clause(&clause).is_some() {
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
        let mut checker1 = Checker::with_clauses(&[
            "not m0(m1(c5, c0), c1)",
            "m4(c4, m1(c5, c0)) != m1(c3, c0) or not m0(m1(c3, c0), c1) or m0(m1(c5, c0), c1) or c4 = c1",
        ]);

        checker1.check_clause_str(
            "m4(c4, m1(c5, c0)) != m1(c3, c0) or not m0(m1(c3, c0), c1) or c4 = c1",
        );

        // This is the basic case plus extra things. So it should also work.
        let mut checker2 = Checker::with_clauses(&[
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
        let mut checker = Checker::with_clauses(&["c0 or c1 or c2", "not c0 or c1", "not c2"]);
        checker.check_clause_str("c1");
    }
}
