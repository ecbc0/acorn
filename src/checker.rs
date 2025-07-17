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
    pub fn insert_clause(&mut self, clause: &Clause) {
        // Only add the clause to the term graph if it has no variables
        if !clause.has_any_variable() {
            self.term_graph
                .insert_clause(clause, StepId(self.next_step_id));
            self.next_step_id += 1;
        }
    }

    /// Returns Some(true) if the clause is known to be true, Some(false) if known false,
    /// and None if we can't tell whether it's true or false.
    pub fn evaluate_clause(&self, clause: &Clause) -> Option<bool> {
        self.term_graph.evaluate_clause(clause)
    }

    /// Returns true if the checker has encountered a contradiction.
    pub fn has_contradiction(&self) -> bool {
        self.term_graph.has_contradiction()
    }
}
