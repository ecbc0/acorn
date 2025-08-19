use std::collections::{HashMap, HashSet};
use std::fmt;

/// Each term has a unique id.
/// We never invent new terms. We only make copies of terms that the caller created and find
/// relationships between them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(pub u32);

impl TermId {
    pub fn get(&self) -> u32 {
        self.0
    }
}

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}

// Each term belongs to a group.
// Terms that belong to the same group are equal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GroupId(pub u32);

impl GroupId {
    pub fn get(&self) -> u32 {
        self.0
    }

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
        write!(f, "id{}", self.get())
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
pub struct ClauseId(pub Vec<LiteralId>);

#[derive(Debug)]
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
                // Index by group
                self.clauses_for_group
                    .entry(literal.left)
                    .or_insert_with(HashSet::new)
                    .insert(clause.clone());
                self.clauses_for_group
                    .entry(literal.right)
                    .or_insert_with(HashSet::new)
                    .insert(clause.clone());
                
                // Index by literal
                self.clauses_for_literal
                    .entry(literal.clone())
                    .or_insert_with(HashSet::new)
                    .insert(clause.clone());
            }
        }
    }

    pub fn contains(&self, clause: &ClauseId) -> bool {
        self.clauses.contains(clause)
    }
    
    /// Removes a clause from the set, including all index entries.
    pub fn remove(&mut self, clause: &ClauseId) -> bool {
        if self.clauses.remove(clause) {
            // Remove from all indices
            for literal in clause.literals() {
                // Remove from group indices
                if let Some(clauses) = self.clauses_for_group.get_mut(&literal.left) {
                    clauses.remove(clause);
                    if clauses.is_empty() {
                        self.clauses_for_group.remove(&literal.left);
                    }
                }
                if let Some(clauses) = self.clauses_for_group.get_mut(&literal.right) {
                    clauses.remove(clause);
                    if clauses.is_empty() {
                        self.clauses_for_group.remove(&literal.right);
                    }
                }
                
                // Remove from literal index
                if let Some(clauses) = self.clauses_for_literal.get_mut(literal) {
                    clauses.remove(clause);
                    if clauses.is_empty() {
                        self.clauses_for_literal.remove(literal);
                    }
                }
            }
            true
        } else {
            false
        }
    }
    
    /// Removes all clauses that contain a specific literal.
    /// Returns the set of clauses that were removed.
    pub fn remove_literal(&mut self, literal: &LiteralId) -> HashSet<ClauseId> {
        // Get all clauses that contain this literal
        let clauses_to_remove = self.clauses_for_literal
            .get(literal)
            .cloned()
            .unwrap_or_else(HashSet::new);
        
        // Remove each clause completely
        for clause in &clauses_to_remove {
            self.remove(clause);
        }
        
        clauses_to_remove
    }
    
    /// Removes all clauses that mention a specific group.
    /// Returns the set of clauses that were removed.
    pub fn remove_group(&mut self, group: GroupId) -> HashSet<ClauseId> {
        // Get all clauses that mention this group
        let clauses_to_remove = self.clauses_for_group
            .get(&group)
            .cloned()
            .unwrap_or_else(HashSet::new);
        
        // Remove each clause completely using the remove method (which handles all indices)
        for clause in &clauses_to_remove {
            self.remove(clause);
        }
        
        clauses_to_remove
    }
    
    /// Validates that the indices are consistent with the main clause set.
    /// Panics if any inconsistency is found.
    pub fn validate(&self) {
        // Check that every clause in clauses appears in the appropriate indices
        for clause in &self.clauses {
            for literal in clause.literals() {
                // Check left group index
                if !self.clauses_for_group
                    .get(&literal.left)
                    .map(|set| set.contains(clause))
                    .unwrap_or(false) 
                {
                    panic!("Clause {:?} not found in clauses_for_group[{:?}]", clause, literal.left);
                }
                // Check right group index  
                if !self.clauses_for_group
                    .get(&literal.right)
                    .map(|set| set.contains(clause))
                    .unwrap_or(false)
                {
                    panic!("Clause {:?} not found in clauses_for_group[{:?}]", clause, literal.right);
                }
                
                // Check literal index
                if !self.clauses_for_literal
                    .get(literal)
                    .map(|set| set.contains(clause))
                    .unwrap_or(false)
                {
                    panic!("Clause {:?} not found in clauses_for_literal[{:?}]", clause, literal);
                }
            }
        }
        
        // Check that every clause in the group indices exists in the main set
        for (group_id, clause_set) in &self.clauses_for_group {
            for clause in clause_set {
                if !self.clauses.contains(clause) {
                    panic!("Clause {:?} in clauses_for_group[{:?}] not found in main clauses set", clause, group_id);
                }
                // Also verify this clause actually mentions this group
                let mentions_group = clause.literals().iter().any(|lit| 
                    lit.left == *group_id || lit.right == *group_id
                );
                if !mentions_group {
                    panic!("Clause {:?} in clauses_for_group[{:?}] doesn't mention that group", clause, group_id);
                }
            }
        }
        
        // Check that every clause in the literal indices exists in the main set
        for (literal_id, clause_set) in &self.clauses_for_literal {
            for clause in clause_set {
                if !self.clauses.contains(clause) {
                    panic!("Clause {:?} in clauses_for_literal[{:?}] not found in main clauses set", clause, literal_id);
                }
                // Also verify this clause actually contains this literal
                let contains_literal = clause.literals().iter().any(|lit| lit == literal_id);
                if !contains_literal {
                    panic!("Clause {:?} in clauses_for_literal[{:?}] doesn't contain that literal", clause, literal_id);
                }
            }
        }
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
                assert_eq!(
                    clause.literals().len(),
                    1,
                    "False literal should be removed"
                );
                assert_eq!(clause.literals()[0], LiteralId::parse("id1 = id2"));
            }
            _ => panic!("Expected Normalization::Clause"),
        }

        // Multiple false literals all get removed
        match ClauseId::parse("id0 != id0 or id1 = id2 or id3 != id3") {
            Normalization::Clause(clause) => {
                assert_eq!(
                    clause.literals().len(),
                    1,
                    "All false literals should be removed"
                );
                assert_eq!(clause.literals()[0], LiteralId::parse("id1 = id2"));
            }
            _ => panic!("Expected Normalization::Clause"),
        }
    }
    
    #[test]
    fn test_clause_set_remove_and_validate() {
        let mut clause_set = ClauseSet::new();
        
        // Insert some clauses
        clause_set.insert_str("id0 = id1 or id2 != id3");
        clause_set.insert_str("id1 = id2");
        clause_set.insert_str("id3 != id4 or id0 = id3");
        
        // Validate should pass
        clause_set.validate();
        
        // Check all clauses are there
        clause_set.check_contains("id0 = id1 or id2 != id3");
        clause_set.check_contains("id1 = id2");
        clause_set.check_contains("id3 != id4 or id0 = id3");
        
        // Remove the middle clause
        let clause_to_remove = ClauseId::parse("id1 = id2").unwrap();
        assert!(clause_set.remove(&clause_to_remove), "Should successfully remove existing clause");
        
        // Validate should still pass after removal
        clause_set.validate();
        
        // Check the removed clause is gone
        assert!(!clause_set.contains(&clause_to_remove), "Removed clause should not be in set");
        
        // Check the other clauses are still there
        clause_set.check_contains("id0 = id1 or id2 != id3");
        clause_set.check_contains("id3 != id4 or id0 = id3");
        
        // Try to remove the same clause again - should return false
        assert!(!clause_set.remove(&clause_to_remove), "Removing non-existent clause should return false");
        
        // Remove another clause with multiple literals
        let multi_clause = ClauseId::parse("id0 = id1 or id2 != id3").unwrap();
        assert!(clause_set.remove(&multi_clause), "Should remove multi-literal clause");
        
        // Validate again
        clause_set.validate();
        
        // Only one clause should remain
        clause_set.check_contains("id3 != id4 or id0 = id3");
        
        // Check that groups are properly cleaned up
        // After removing "id0 = id1 or id2 != id3" and "id1 = id2",
        // id1 and id2 should no longer be in clauses_for_group (unless in remaining clause)
        let remaining_groups: Vec<_> = clause_set.clauses_for_group.keys().cloned().collect();
        assert!(remaining_groups.contains(&GroupId::parse("id0")));
        assert!(remaining_groups.contains(&GroupId::parse("id3")));
        assert!(remaining_groups.contains(&GroupId::parse("id4")));
        // id1 and id2 should be gone since they're not in the remaining clause
        assert!(!remaining_groups.contains(&GroupId::parse("id1")));
        assert!(!remaining_groups.contains(&GroupId::parse("id2")));
    }
    
    #[test]
    fn test_clause_set_remove_literal() {
        let mut clause_set = ClauseSet::new();
        
        // Insert several clauses with various literals
        clause_set.insert_str("id0 = id1");
        clause_set.insert_str("id1 = id2 or id3 != id4");  
        clause_set.insert_str("id2 != id3");  
        clause_set.insert_str("id4 = id5");
        clause_set.insert_str("id0 != id2 or id1 = id3");  
        clause_set.insert_str("id1 = id2 or id5 != id6"); // Another clause with "id1 = id2"
        
        // Validate initial state
        clause_set.validate();
        
        // Remove all clauses containing the literal "id1 = id2"
        let literal_to_remove = LiteralId::parse("id1 = id2");
        let removed = clause_set.remove_literal(&literal_to_remove);
        
        // Should have removed 2 clauses
        assert_eq!(removed.len(), 2, "Should remove 2 clauses that contain 'id1 = id2'");
        
        // Check the removed clauses are the right ones
        assert!(removed.contains(&ClauseId::parse("id1 = id2 or id3 != id4").unwrap()));
        assert!(removed.contains(&ClauseId::parse("id1 = id2 or id5 != id6").unwrap()));
        
        // Validate after removal
        clause_set.validate();
        
        // Check remaining clauses
        clause_set.check_contains("id0 = id1");
        clause_set.check_contains("id2 != id3");
        clause_set.check_contains("id4 = id5");
        clause_set.check_contains("id0 != id2 or id1 = id3");
        
        // Check that removed clauses are gone
        assert!(!clause_set.contains(&ClauseId::parse("id1 = id2 or id3 != id4").unwrap()));
        assert!(!clause_set.contains(&ClauseId::parse("id1 = id2 or id5 != id6").unwrap()));
        
        // Remove a literal that doesn't exist
        let nonexistent_literal = LiteralId::parse("id99 = id100");
        let empty_removal = clause_set.remove_literal(&nonexistent_literal);
        assert!(empty_removal.is_empty(), "Removing non-existent literal should return empty set");
        
        // Validate still works
        clause_set.validate();
        
        // Remove another literal "id2 != id3"
        let another_literal = LiteralId::parse("id2 != id3");
        let removed2 = clause_set.remove_literal(&another_literal);
        
        // Should have removed 1 clause
        assert_eq!(removed2.len(), 1, "Should remove 1 clause that contains 'id2 != id3'");
        assert!(removed2.contains(&ClauseId::parse("id2 != id3").unwrap()));
        
        // Validate final state
        clause_set.validate();
        
        // Check final remaining clauses
        clause_set.check_contains("id0 = id1");
        clause_set.check_contains("id4 = id5");
        clause_set.check_contains("id0 != id2 or id1 = id3");
    }
    
    #[test]
    fn test_clause_set_remove_group() {
        let mut clause_set = ClauseSet::new();
        
        // Insert several clauses, some mentioning id2
        clause_set.insert_str("id0 = id1");
        clause_set.insert_str("id1 = id2 or id3 != id4");  // mentions id2
        clause_set.insert_str("id2 != id3");  // mentions id2
        clause_set.insert_str("id4 = id5");
        clause_set.insert_str("id0 != id2 or id1 = id3");  // mentions id2
        
        // Validate initial state
        clause_set.validate();
        
        // Remove all clauses mentioning id2
        let removed = clause_set.remove_group(GroupId::parse("id2"));
        
        // Should have removed 3 clauses
        assert_eq!(removed.len(), 3, "Should remove 3 clauses that mention id2");
        
        // Check the removed clauses are the right ones
        assert!(removed.contains(&ClauseId::parse("id1 = id2 or id3 != id4").unwrap()));
        assert!(removed.contains(&ClauseId::parse("id2 != id3").unwrap()));
        assert!(removed.contains(&ClauseId::parse("id0 != id2 or id1 = id3").unwrap()));
        
        // Validate after removal - this is the key test
        clause_set.validate();
        
        // Check remaining clauses
        clause_set.check_contains("id0 = id1");
        clause_set.check_contains("id4 = id5");
        
        // Check that removed clauses are gone
        assert!(!clause_set.contains(&ClauseId::parse("id1 = id2 or id3 != id4").unwrap()));
        assert!(!clause_set.contains(&ClauseId::parse("id2 != id3").unwrap()));
        assert!(!clause_set.contains(&ClauseId::parse("id0 != id2 or id1 = id3").unwrap()));
        
        // Check that id2 is completely gone from indices
        assert!(!clause_set.clauses_for_group.contains_key(&GroupId::parse("id2")));
        
        // Groups that should still be present (from remaining clauses)
        assert!(clause_set.clauses_for_group.contains_key(&GroupId::parse("id0")));
        assert!(clause_set.clauses_for_group.contains_key(&GroupId::parse("id1")));
        assert!(clause_set.clauses_for_group.contains_key(&GroupId::parse("id4")));
        assert!(clause_set.clauses_for_group.contains_key(&GroupId::parse("id5")));
        
        // id3 should be gone since all clauses mentioning it were removed
        assert!(!clause_set.clauses_for_group.contains_key(&GroupId::parse("id3")));
        
        // Test removing a group that doesn't exist
        let empty_removal = clause_set.remove_group(GroupId::parse("id99"));
        assert!(empty_removal.is_empty(), "Removing non-existent group should return empty set");
        
        // Validate still works after removing non-existent group
        clause_set.validate();
    }
}
