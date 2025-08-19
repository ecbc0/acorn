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

impl Normalization {
    fn unwrap(self) -> ClauseId {
        match self {
            Normalization::True | Normalization::False => {
                panic!("Normalization::unwrap called on non-clause variant")
            }
            Normalization::Clause(clause) => clause,
        }
    }

    /// Asserts that this normalization is True (tautology).
    /// Panics if it's False or a Clause.
    pub fn assert_true(&self) {
        match self {
            Normalization::True => {}
            Normalization::False => panic!("Expected Normalization::True but got False"),
            Normalization::Clause(clause) => {
                panic!("Expected Normalization::True but got Clause: {}", clause)
            }
        }
    }

    /// Asserts that this normalization is False (contradiction).
    /// Panics if it's True or a Clause.
    pub fn assert_false(&self) {
        match self {
            Normalization::False => {}
            Normalization::True => panic!("Expected Normalization::False but got True"),
            Normalization::Clause(clause) => {
                panic!("Expected Normalization::False but got Clause: {}", clause)
            }
        }
    }
}

impl ClauseId {
    /// Creates a normalized clause from literals.
    /// Returns Normalization::True if the clause is a tautology (contains both x and !x or id = id).
    /// Returns Normalization::False if the clause is empty.
    /// Otherwise returns Normalization::Clause with sorted, deduplicated literals.
    pub fn new(mut literals: Vec<LiteralId>) -> Normalization {
        literals.sort();
        literals.dedup();

        // Filter out reflexive literals and check for tautologies
        let mut filtered_literals = Vec::new();
        for lit in literals {
            if lit.left == lit.right {
                if lit.positive {
                    // id = id is always true, making the whole clause true
                    return Normalization::True;
                }
                // id != id is always false, skip it (don't add to filtered)
            } else {
                filtered_literals.push(lit);
            }
        }
        literals = filtered_literals;

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

    /// Parses a string like "id0 = id1" or "id0 = id1 or id2 != id3" into a Normalization.
    /// Returns the appropriate variant based on the clause content.
    /// Panics if the format is invalid.
    pub fn parse(s: &str) -> Normalization {
        let literals: Vec<LiteralId> = s
            .split(" or ")
            .map(|lit_str| LiteralId::parse(lit_str.trim()))
            .collect();

        ClauseId::new(literals)
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
    /// Panics if the string format is invalid or if the parsed result is True/False.
    pub fn insert_str(&mut self, s: &str) {
        let clause = ClauseId::parse(s).unwrap();
        self.insert(clause);
    }

    /// Checks if the clause set contains a clause parsed from the string.
    /// Panics if the clause is not found or if the parsed result is True/False.
    pub fn check_contains(&self, s: &str) {
        let clause = ClauseId::parse(s).unwrap();
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
        // "id0 = id1 or id0 = id1 or id2 != id3" should deduplicate to just 2 literals
        match ClauseId::parse("id0 = id1 or id0 = id1 or id2 != id3") {
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
        ClauseId::parse("id0 = id1 or id0 != id1").assert_true();
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

    #[test]
    fn test_reflexive_equality_is_tautology() {
        // "id0 = id0" should be recognized as a tautology (always true)
        ClauseId::parse("id0 = id0").assert_true();
        
        // Same for more complex clauses - if any literal is reflexively true, whole clause is true
        ClauseId::parse("id0 != id1 or id2 = id2").assert_true();
        ClauseId::parse("id5 = id5 or id3 != id4").assert_true();
    }

    #[test]
    fn test_reflexive_inequality_removed() {
        // "id0 != id0" is always false, so it should be removed from the clause
        // A clause with just "id0 != id0" becomes empty (False)
        ClauseId::parse("id0 != id0").assert_false();
        
        // When combined with other literals, the false literal is removed
        match ClauseId::parse("id0 != id0 or id1 = id2") {
            Normalization::Clause(clause) => {
                assert_eq!(clause.literals().len(), 1, "False literal should be removed");
                assert_eq!(clause.literals()[0], LiteralId::parse("id1 = id2"));
            }
            _ => panic!("Expected Normalization::Clause"),
        }
        
        // Multiple false literals all get removed
        match ClauseId::parse("id0 != id0 or id1 = id2 or id3 != id3") {
            Normalization::Clause(clause) => {
                assert_eq!(clause.literals().len(), 1, "All false literals should be removed");
                assert_eq!(clause.literals()[0], LiteralId::parse("id1 = id2"));
            }
            _ => panic!("Expected Normalization::Clause"),
        }
    }
}
