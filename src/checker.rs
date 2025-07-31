use crate::clause::Clause;
use crate::clause_set::ClauseSet;
use crate::term_graph::{StepId, TermGraph};

/// The checker quickly checks if a clause can be proven in a single step from known clauses.
#[derive(Clone)]
pub struct Checker {
    term_graph: TermGraph,
    clause_set: ClauseSet,
    next_step_id: usize,
}

impl Checker {
    pub fn new() -> Self {
        Checker {
            term_graph: TermGraph::new(),
            clause_set: ClauseSet::new(),
            next_step_id: 0,
        }
    }

    /// Adds a true clause to the checker.
    pub fn insert_clause(&mut self, clause: &Clause) {
        let step_id = self.next_step_id;
        self.next_step_id += 1;

        if !clause.has_any_variable() {
            // Add concrete clauses to the term graph for fast evaluation
            self.term_graph.insert_clause(clause, StepId(step_id));
        } else {
            // Add clauses with variables to the clause set
            self.clause_set.insert(clause.clone(), step_id);

            // Also add all equality resolution clauses
            let resolutions = clause.equality_resolutions();
            for resolution in resolutions {
                self.insert_clause(&resolution);
            }
        }
    }

    /// Returns true if the clause is known to be true.
    pub fn check_clause(&self, clause: &Clause) -> bool {
        // First check the term graph for concrete evaluation
        if self.term_graph.evaluate_clause(clause) == Some(true) {
            return true;
        }

        // If not found in term graph, check if there's a generalization in the clause set
        if self
            .clause_set
            .find_generalization(clause.clone())
            .is_some()
        {
            return true;
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
        self.term_graph.has_contradiction()
    }
}
