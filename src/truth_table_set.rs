use std::collections::HashMap;

use crate::clause::Clause;

/// A set that stores clauses by their truth table representation.
/// Each clause is stored with its normalized positive form as the key,
/// and all the polarity patterns that have been seen for that clause.
pub struct TruthTableSet {
    /// Maps from normalized positive clauses to sets of polarity patterns
    tables: HashMap<Clause, Vec<Vec<bool>>>,
}

impl TruthTableSet {
    /// Creates a new empty TruthTableSet
    pub fn new() -> Self {
        TruthTableSet {
            tables: HashMap::new(),
        }
    }

    /// Inserts a clause into the set.
    /// Extracts the polarity pattern and stores it under the normalized positive clause.
    pub fn insert(&mut self, clause: &Clause) {
        let (positive_clause, polarities) = clause.extract_polarity();
        
        self.tables
            .entry(positive_clause)
            .or_insert_with(Vec::new)
            .push(polarities);
    }

    /// Checks if a clause is contained in the set.
    /// Returns true if the exact polarity pattern exists for this clause.
    pub fn contains(&self, clause: &Clause) -> bool {
        let (positive_clause, polarities) = clause.extract_polarity();
        
        if let Some(polarity_sets) = self.tables.get(&positive_clause) {
            polarity_sets.contains(&polarities)
        } else {
            false
        }
    }
}