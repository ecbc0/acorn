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
    /// Parses a string like "g7" into GroupId(7).
    /// Panics if the string doesn't start with "g" followed by a valid number.
    pub fn parse(s: &str) -> GroupId {
        if !s.starts_with('g') {
            panic!(
                "GroupId::parse expects string starting with 'g', got: {}",
                s
            );
        }
        let num = s[1..].parse::<u32>().unwrap_or_else(|_| {
            panic!(
                "GroupId::parse expects 'g' followed by a number, got: {}",
                s
            )
        });
        GroupId(num)
    }
}

impl fmt::Display for GroupId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
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
