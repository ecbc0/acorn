use crate::clause::Clause;
use crate::generalization_set::GeneralizationSet;
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
