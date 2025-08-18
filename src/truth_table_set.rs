use std::collections::HashMap;

use crate::{clause::Clause, literal::Literal};

/// A set that stores clauses by their truth table representation.
/// Each clause is stored with its normalized positive form as the key,
/// and all the polarity patterns that have been seen for that clause.
pub struct TruthTableSet {
    /// Maps from normalized positive clauses to sets of polarity patterns
    tables: HashMap<Clause, Vec<Vec<bool>>>,
}

// If the two bit vectors differ in exactly one spot, return the index of that spot.
// Otherwise return None.
fn find_different_bit(a: &Vec<bool>, b: &Vec<bool>) -> Option<usize> {
    if a.len() != b.len() {
        return None;
    }

    let mut diff_index = None;
    for (i, (a_bit, b_bit)) in a.iter().zip(b.iter()).enumerate() {
        if a_bit != b_bit {
            if diff_index.is_some() {
                // Different in multiple spots
                return None;
            }
            diff_index = Some(i);
        }
    }

    diff_index
}

// Removes the literal at the given index from the positive clause and adds back in polarities.
// This does normalize the resulting clause.
fn eliminate_literal(positive_clause: &Clause, polarities: &Vec<bool>, index: usize) -> Clause {
    let mut literals = vec![];
    for (i, (lit, pol)) in positive_clause
        .literals
        .iter()
        .zip(polarities.iter())
        .enumerate()
    {
        if i == index {
            continue;
        }
        literals.push(Literal::new(*pol, lit.left.clone(), lit.right.clone()));
    }
    Clause::new(literals)
}

impl TruthTableSet {
    /// Creates a new empty TruthTableSet
    pub fn new() -> Self {
        TruthTableSet {
            tables: HashMap::new(),
        }
    }

    /// Inserts a clause into the set if it doesn't already exist.
    /// Extracts the polarity pattern and stores it under the normalized positive clause.
    /// Does not insert duplicates.
    ///
    /// When there are any other clauses which differ in exactly one spot, you can deduce that
    /// the clause without this differing literal must also be true. This method returns all
    /// clauses that can be deduced in such a way.
    ///
    /// When we insert a duplicate, no deduced clauses are returned.
    pub fn insert(&mut self, clause: &Clause) -> Vec<Clause> {
        let (positive_clause, new_pol) = clause.extract_polarity();

        let entry = match self.tables.entry(positive_clause) {
            std::collections::hash_map::Entry::Occupied(entry) => entry,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(vec![new_pol]);
                return vec![];
            }
        };
        let key = entry.key();
        let known_pols = entry.get();
        if known_pols.contains(&new_pol) {
            // Already exists, no need to insert
            return vec![];
        }

        let mut answer = vec![];
        for pol in known_pols.iter() {
            if let Some(i) = find_different_bit(pol, &new_pol) {
                let new_clause = eliminate_literal(key, &new_pol, i);
                answer.push(new_clause);
            }
        }

        entry.into_mut().push(new_pol);
        answer
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_duplicates() {
        let mut set = TruthTableSet::new();

        // Create some sample clauses using c0, c1, etc. for constants
        let clause1 = Clause::parse("c0 = c1 or c2 = c3");
        let clause2 = Clause::parse("c0 != c1 or c2 = c3");
        let clause3 = Clause::parse("c0 = c1 or c2 != c3");

        // Insert clause1 twice
        set.insert(&clause1);
        set.insert(&clause1);

        // Check that clause1 is in the set
        assert!(set.contains(&clause1));

        // Check that there's only one entry for the positive form of clause1
        let (positive_clause, _) = clause1.extract_polarity();
        let polarity_sets = set.tables.get(&positive_clause).unwrap();
        assert_eq!(
            polarity_sets.len(),
            1,
            "Should not have duplicate polarity patterns"
        );

        // Insert different clauses with different polarities
        set.insert(&clause2);
        set.insert(&clause3);

        // All three should be in the set
        assert!(set.contains(&clause1));
        assert!(set.contains(&clause2));
        assert!(set.contains(&clause3));

        // Insert clause2 again
        set.insert(&clause2);

        // Check that we still have the right number of patterns
        // clause2 and clause3 might map to the same positive clause or different ones
        // depending on the ordering of literals
        for (_, polarity_sets) in &set.tables {
            // Check that no polarity pattern is duplicated within a clause
            for i in 0..polarity_sets.len() {
                for j in i + 1..polarity_sets.len() {
                    assert_ne!(
                        polarity_sets[i], polarity_sets[j],
                        "Should not have duplicate polarity patterns for same clause"
                    );
                }
            }
        }
    }

    #[test]
    fn test_same_literals_different_polarities() {
        let mut set = TruthTableSet::new();

        // These have the same literals but different polarities
        let clause1 = Clause::parse("c0 = c1 or c2 = c3");
        let clause2 = Clause::parse("c0 != c1 or c2 != c3");
        let clause3 = Clause::parse("c0 = c1 or c2 != c3");
        let clause4 = Clause::parse("c0 != c1 or c2 = c3");

        set.insert(&clause1);
        set.insert(&clause2);
        set.insert(&clause3);
        set.insert(&clause4);

        // All should be contained
        assert!(set.contains(&clause1));
        assert!(set.contains(&clause2));
        assert!(set.contains(&clause3));
        assert!(set.contains(&clause4));

        // Try inserting them again - should not create duplicates
        set.insert(&clause1);
        set.insert(&clause2);
        set.insert(&clause3);
        set.insert(&clause4);

        // Still all contained
        assert!(set.contains(&clause1));
        assert!(set.contains(&clause2));
        assert!(set.contains(&clause3));
        assert!(set.contains(&clause4));

        // Check that we have exactly 4 polarity patterns total
        let total_patterns: usize = set.tables.values().map(|v| v.len()).sum();
        assert_eq!(
            total_patterns, 4,
            "Should have exactly 4 unique polarity patterns"
        );
    }
}
