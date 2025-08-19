use std::collections::{HashMap, HashSet};
use std::fmt;

/// Each term has a unique id.
/// We never invent new terms. We only make copies of terms that the caller created and find
/// relationships between them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(pub u32);

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// Each term belongs to a group.
// Terms that belong to the same group are equal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GroupId(pub u32);

impl GroupId {
    /// Parses a string like "id7" into GroupId(7).
    /// Panics if the string doesn't start with "id" followed by a valid number.
    pub fn parse(s: &str) -> GroupId {
        if !s.starts_with("id") {
            panic!(
                "GroupId::parse expects string starting with 'id', got: {}",
                s
            );
        }
        let num = s[2..].parse::<u32>().unwrap_or_else(|_| {
            panic!(
                "GroupId::parse expects 'id' followed by a number, got: {}",
                s
            )
        });
        GroupId(num)
    }
}

impl fmt::Display for GroupId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "id{}", self.0)
    }
}

// Canonically the group ids are sorted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LiteralId {
    pub left: GroupId,
    pub right: GroupId,
    pub positive: bool,
}

impl LiteralId {
    pub fn new(left: GroupId, right: GroupId, positive: bool) -> Self {
        if left <= right {
            LiteralId {
                left,
                right,
                positive,
            }
        } else {
            LiteralId {
                left: right,
                right: left,
                positive,
            }
        }
    }

    /// Parses a string like "id0 = id1" or "id1 != id2" into a LiteralId.
    /// Panics if the format is invalid.
    pub fn parse(s: &str) -> LiteralId {
        // Try to split on " != " first (longer operator)
        if let Some((left_str, right_str)) = s.split_once(" != ") {
            let left = GroupId::parse(left_str.trim());
            let right = GroupId::parse(right_str.trim());
            LiteralId::new(left, right, false)
        } else if let Some((left_str, right_str)) = s.split_once(" = ") {
            let left = GroupId::parse(left_str.trim());
            let right = GroupId::parse(right_str.trim());
            LiteralId::new(left, right, true)
        } else {
            panic!(
                "LiteralId::parse expects format 'id0 = id1' or 'id0 != id1', got: {}",
                s
            );
        }
    }
}

impl fmt::Display for LiteralId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.positive {
            write!(f, "{} = {}", self.left, self.right)
        } else {
            write!(f, "{} != {}", self.left, self.right)
        }
    }
}

// Canonically the literal ids are sorted.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ClauseId(Vec<LiteralId>);

pub enum Normalization {
    True,
    False,
    Clause(ClauseId),
}

impl ClauseId {
    /// Creates a normalized clause from literals.
    /// Returns Normalization::True if the clause is a tautology (contains both x and !x).
    /// Returns Normalization::False if the clause is empty.
    /// Otherwise returns Normalization::Clause with sorted, deduplicated literals.
    pub fn new(mut literals: Vec<LiteralId>) -> Normalization {
        literals.sort();
        literals.dedup();

        // Check if empty (contradiction)
        if literals.is_empty() {
            return Normalization::False;
        }

        // Check for tautology: same left/right groups but opposite polarity
        for i in 0..literals.len() {
            for j in i + 1..literals.len() {
                if literals[i].left == literals[j].left
                    && literals[i].right == literals[j].right
                    && literals[i].positive != literals[j].positive
                {
                    return Normalization::True;
                }
            }
        }

        Normalization::Clause(ClauseId(literals))
    }

    pub fn literals(&self) -> &Vec<LiteralId> {
        &self.0
    }

    /// Parses a string like "id0 = id1" or "id0 = id1 or id2 != id3" into a ClauseId.
    /// Panics if the format is invalid.
    pub fn parse(s: &str) -> ClauseId {
        let literals: Vec<LiteralId> = s
            .split(" or ")
            .map(|lit_str| LiteralId::parse(lit_str.trim()))
            .collect();

        if literals.is_empty() {
            panic!("ClauseId::parse expects at least one literal, got empty string");
        }

        // Create a ClauseId directly with sorted and deduped literals
        let mut literals = literals;
        literals.sort();
        literals.dedup();
        ClauseId(literals)
    }
}

impl fmt::Display for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0.is_empty() {
            write!(f, "(empty clause)")
        } else {
            for (i, literal) in self.0.iter().enumerate() {
                if i > 0 {
                    write!(f, " or ")?;
                }
                write!(f, "{}", literal)?;
            }
            Ok(())
        }
    }
}

#[derive(Clone)]
pub struct ClauseSet {
    clauses: HashSet<ClauseId>,
    clauses_for_group: HashMap<GroupId, HashSet<ClauseId>>,
    clauses_for_literal: HashMap<LiteralId, HashSet<ClauseId>>,
}

impl ClauseSet {
    pub fn new() -> Self {
        ClauseSet {
            clauses: HashSet::new(),
            clauses_for_group: HashMap::new(),
            clauses_for_literal: HashMap::new(),
        }
    }

    pub fn insert(&mut self, clause: ClauseId) {
        if self.clauses.insert(clause.clone()) {
            for literal in clause.literals() {
                self.clauses_for_literal
                    .entry(literal.clone())
                    .or_insert_with(HashSet::new)
                    .insert(clause.clone());
                self.clauses_for_group
                    .entry(literal.left)
                    .or_insert_with(HashSet::new)
                    .insert(clause.clone());
                self.clauses_for_group
                    .entry(literal.right)
                    .or_insert_with(HashSet::new)
                    .insert(clause.clone());
            }
        }
    }

    pub fn contains(&self, clause: &ClauseId) -> bool {
        self.clauses.contains(clause)
    }

    /// Inserts a clause by parsing it from a string.
    /// Panics if the string format is invalid.
    pub fn insert_str(&mut self, s: &str) {
        let clause = ClauseId::parse(s);
        self.insert(clause);
    }

    /// Checks if the clause set contains a clause parsed from the string.
    /// Panics if the clause is not found or if the string format is invalid.
    pub fn check_contains(&self, s: &str) {
        let clause = ClauseId::parse(s);
        if !self.contains(&clause) {
            panic!("ClauseSet does not contain clause: {}", s);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clause_deduplication() {
        // Test that duplicate literals are removed
        let literals = vec![
            LiteralId::parse("id0 = id1"),
            LiteralId::parse("id0 = id1"), // duplicate
            LiteralId::parse("id2 != id3"),
        ];

        match ClauseId::new(literals) {
            Normalization::Clause(clause) => {
                assert_eq!(
                    clause.literals().len(),
                    2,
                    "Should deduplicate to 2 literals"
                );
                // Verify the literals are sorted and correct
                assert_eq!(clause.literals()[0], LiteralId::parse("id0 = id1"));
                assert_eq!(clause.literals()[1], LiteralId::parse("id2 != id3"));
            }
            _ => panic!("Expected Normalization::Clause"),
        }
    }

    #[test]
    fn test_clause_tautology() {
        // Test that "id0 = id1 or id0 != id1" is recognized as a tautology
        let literals = vec![
            LiteralId::parse("id0 = id1"),
            LiteralId::parse("id0 != id1"),
        ];

        match ClauseId::new(literals) {
            Normalization::True => {} // Expected
            _ => panic!("Expected Normalization::True for tautology"),
        }
    }

    #[test]
    fn test_clause_set_helpers() {
        let mut clause_set = ClauseSet::new();

        // Insert a clause using the string helper
        clause_set.insert_str("id0 = id1 or id2 != id3");

        // Check it's there using the check helper (should not panic)
        clause_set.check_contains("id0 = id1 or id2 != id3");

        // Check that reordered literals still match (due to canonicalization)
        clause_set.check_contains("id2 != id3 or id0 = id1");
    }
}
