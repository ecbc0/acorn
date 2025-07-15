use crate::clause::Clause;

/// The checker quickly checks if a clause can be proven in a single step from known clauses.
#[derive(Clone)]
pub struct Checker {}

impl Checker {
    pub fn new() -> Self {
        Checker {}
    }

    pub fn add_clause(&mut self, _clause: &Clause) {
        // TODO: use the clause
    }

    pub fn check_clause(&self, _clause: &Clause) -> bool {
        todo!()
    }
}
