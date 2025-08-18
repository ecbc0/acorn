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
            panic!("LiteralId::parse expects format 'id0 = id1' or 'id0 != id1', got: {}", s);
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
    // This sorts the literals, but doesn't check for degeneracy like repeating literals.
    pub fn new(mut literals: Vec<LiteralId>) -> Normalization {
        literals.sort();
        literals.dedup();
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
}
