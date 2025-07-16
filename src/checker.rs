use crate::clause::Clause;
use crate::term_graph::{StepId, TermGraph};

/// The checker quickly checks if a clause can be proven in a single step from known clauses.
#[derive(Clone)]
pub struct Checker {
    term_graph: TermGraph,
    next_step_id: usize,
}

impl Checker {
    pub fn new() -> Self {
        Checker {
            term_graph: TermGraph::new(),
            next_step_id: 0,
        }
    }

    /// Adds a true clause to the checker.
    pub fn add_clause(&mut self, clause: &Clause) {
        // Only add the clause to the term graph if it has no variables
        if !clause.has_any_variable() {
            self.term_graph
                .insert_clause(clause, StepId(self.next_step_id));
            self.next_step_id += 1;
        }
    }

    /// Returns true if the clause can be proven in a single step from the known clauses.
    pub fn check_clause(&self, clause: &Clause) -> bool {
        if clause.literals.len() == 1 {
            if self.term_graph.evaluate_literal(&clause.literals[0]) == Some(true) {
                return true;
            }
        }
        // We can't evaluate
        false
    }

    /// Returns true if the checker has encountered a contradiction.
    pub fn has_contradiction(&self) -> bool {
        self.term_graph.has_contradiction()
    }
}
