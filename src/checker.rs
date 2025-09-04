use std::borrow::Cow;

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
use crate::normalizer::Normalizer;
use crate::project::Project;
use crate::stack::Stack;
use crate::statement::{Statement, StatementInfo};
use crate::term_graph::{StepId, TermGraph};

/// The checker quickly checks if a clause can be proven in a single step from known clauses.
#[derive(Clone)]
pub struct Checker {
    /// For deductions among concrete clauses.
    term_graph: TermGraph,

    /// For looking up specializations of clauses with free variables.
    generalization_set: GeneralizationSet,

    next_step_id: usize,

    /// Whether a contradiction was directly inserted into the checker.
    direct_contradiction: bool,

    /// Whether to track clause insertions in verbose mode.
    verbose: bool,

    /// Stringified versions of inserted clauses when verbose is true.
    insertions: Vec<String>,
}

impl Checker {
    pub fn new() -> Self {
        Checker {
            term_graph: TermGraph::new(),
            generalization_set: GeneralizationSet::new(),
            next_step_id: 0,
            direct_contradiction: false,
            verbose: false,
            insertions: Vec::new(),
        }
    }

    pub fn new_verbose() -> Self {
        let mut c = Checker::new();
        c.verbose = true;
        c
    }

    /// Adds a true clause to the checker.
    pub fn insert_clause(&mut self, clause: &Clause) {
        if self.verbose {
            self.insertions.push(clause.to_string());
        }

        if clause.is_impossible() {
            self.direct_contradiction = true;
            return;
        }

        let step_id = self.next_step_id;
        self.next_step_id += 1;

        if clause.has_any_variable() {
            // The clause has free variables, so it can be a generalization.
            self.generalization_set.insert(clause.clone(), step_id);

            // We only need to do equality resolution for clauses with free variables,
            // because resolvable concrete literals would already have been simplified out.
            for resolution in clause.equality_resolutions() {
                self.insert_clause(&resolution);
            }
        } else {
            // The clause is concrete.

            // The term graph does all sorts of stuff but only for concrete clauses.
            self.term_graph.insert_clause(clause, StepId(step_id));
        }

        for factoring in clause.equality_factorings() {
            self.insert_clause(&factoring);
        }

        for elim in clause.function_eliminations() {
            self.insert_clause(&elim);
        }
    }

    /// Returns true if the clause is known to be true.
    /// If we have found any contradiction, we can degenerately conclude the clause is true.
    pub fn check_clause(&mut self, clause: &Clause) -> bool {
        if self.has_contradiction() {
            return true;
        }

        // Check the term graph for concrete evaluation
        if self.term_graph.check_clause(clause) {
            return true;
        }

        // If not found in term graph, check if there's a generalization in the clause set
        if self
            .generalization_set
            .find_generalization(clause.clone())
            .is_some()
        {
            return true;
        }

        if self.verbose {
            println!("With Checker::with_clauses(&[");
            for insertion in &self.insertions {
                println!("    \"{}\",", insertion);
            }
            println!("]);");
            println!("Failed check: \"{}\"", clause);
        }

        false
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

                // Create an exists value
                let types = decls.iter().map(|(_, ty)| ty.clone()).collect();

                if condition_value != AcornValue::Bool(true) {
                    let exists_value = AcornValue::exists(types, condition_value);

                    // Check if this matches any existing skolem
                    let Some(_info) = normalizer.find_exact_skolem_info(&exists_value) else {
                        return Err(Error::GeneratedBadCode(
                            "let...satisfy statement does not match any skolem definition"
                                .to_string(),
                        ));
                    };
                }

                // Add all the variables in decls to the bindings and the normalizer
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

                // Re-parse the expression with the newly defined variables
                let mut evaluator = Evaluator::new(project, bindings, None);
                let value = evaluator.evaluate_value(&vss.condition, Some(&AcornType::Bool))?;
                let clauses = normalizer.clauses_from_value(&value)?;
                for mut clause in clauses {
                    clause.normalize();
                    self.insert_clause(&clause);
                }
                Ok(())
            }
            StatementInfo::Claim(claim) => {
                let value = evaluator.evaluate_value(&claim.claim, Some(&AcornType::Bool))?;
                let clauses = normalizer.clauses_from_value(&value)?;

                for mut clause in clauses {
                    if !self.check_clause(&clause) {
                        return Err(Error::GeneratedBadCode(format!(
                            "The clause '{}' is not obviously true",
                            clause
                        )));
                    }
                    clause.normalize();
                    self.insert_clause(&clause);
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
    pub fn check_cert(
        &mut self,
        cert: &Certificate,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Normalizer,
    ) -> Result<(), Error> {
        let Some(proof) = &cert.proof else {
            return Err(Error::NoProof);
        };
        for code in proof {
            if self.has_contradiction() {
                return Ok(());
            }
            self.check_code(code, project, bindings, normalizer)?;
        }

        if self.has_contradiction() {
            Ok(())
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
            checker.insert_clause(&clause);
        }
        checker
    }

    #[cfg(test)]
    pub fn check_clause_str(&mut self, s: &str) {
        let clause = Clause::parse(s);
        if !self.check_clause(&clause) {
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
