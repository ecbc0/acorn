use serde::{Deserialize, Serialize};

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::context::Context;
use crate::kernel::fat_term::TypeId;
use crate::kernel::thin_term::ThinTerm;

/// A thin literal stores the structure of a literal without type information.
/// Like Literal, it represents an equation (or inequality) between two terms.
/// Type information is stored separately in the TypeStore and SymbolTable.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct ThinLiteral {
    pub positive: bool,
    pub left: ThinTerm,
    pub right: ThinTerm,
}

impl ThinLiteral {
    pub fn new(positive: bool, left: ThinTerm, right: ThinTerm) -> ThinLiteral {
        ThinLiteral {
            positive,
            left,
            right,
        }
    }

    /// Create a positive literal from a single term (term = true).
    pub fn positive(term: ThinTerm) -> ThinLiteral {
        ThinLiteral::new(true, term, ThinTerm::atom(Atom::True))
    }

    /// Create a negative literal from a single term (not term, i.e., term != true).
    pub fn negative(term: ThinTerm) -> ThinLiteral {
        ThinLiteral::new(false, term, ThinTerm::atom(Atom::True))
    }

    /// Create an equality literal (left = right).
    pub fn equals(left: ThinTerm, right: ThinTerm) -> ThinLiteral {
        ThinLiteral::new(true, left, right)
    }

    /// Create an inequality literal (left != right).
    pub fn not_equals(left: ThinTerm, right: ThinTerm) -> ThinLiteral {
        ThinLiteral::new(false, left, right)
    }

    /// Negate this literal (flip positive/negative).
    pub fn negate(&self) -> ThinLiteral {
        ThinLiteral {
            positive: !self.positive,
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }

    /// Check if this literal is a tautology (foo = foo with positive=true).
    pub fn is_tautology(&self) -> bool {
        self.positive && self.left == self.right
    }

    /// Check if this literal is impossible (foo != foo).
    pub fn is_impossible(&self) -> bool {
        !self.positive && self.left == self.right
    }

    /// Check if this is a signed term (right side is "true").
    pub fn is_signed_term(&self) -> bool {
        self.right.is_true()
    }

    /// Check if this literal contains any variables.
    pub fn has_any_variable(&self) -> bool {
        self.left.has_any_variable() || self.right.has_any_variable()
    }

    /// Check if this literal contains any local constants.
    pub fn has_local_constant(&self) -> bool {
        self.left.has_local_constant() || self.right.has_local_constant()
    }

    /// Count the total number of atoms in both terms.
    pub fn atom_count(&self) -> u32 {
        self.left.atom_count() + self.right.atom_count()
    }

    /// Get the type of a variable if it appears in this literal.
    pub fn var_type(&self, i: AtomId, context: &Context) -> Option<TypeId> {
        // Check if the variable appears in left or right term
        if self.left.has_variable(i) || self.right.has_variable(i) {
            context.get_var_type(i as usize)
        } else {
            None
        }
    }

    /// Apply a function to both terms in this literal.
    pub fn map(&self, f: &mut impl FnMut(&ThinTerm) -> ThinTerm) -> ThinLiteral {
        ThinLiteral::new(self.positive, f(&self.left), f(&self.right))
    }

    /// Replace an atom with another atom in both terms.
    pub fn replace_atom(&self, atom: &Atom, replacement: &Atom) -> ThinLiteral {
        ThinLiteral {
            positive: self.positive,
            left: self.left.replace_atom(atom, replacement),
            right: self.right.replace_atom(atom, replacement),
        }
    }

    /// Get the least unused variable index across both terms.
    pub fn least_unused_variable(&self) -> AtomId {
        self.left
            .least_unused_variable()
            .max(self.right.least_unused_variable())
    }

    /// Iterate over all atoms in both terms.
    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom> + '_ {
        self.left.iter_atoms().chain(self.right.iter_atoms())
    }

    /// Check if these two literals are negations of each other.
    pub fn equals_negated(&self, other: &ThinLiteral) -> bool {
        self.positive != other.positive && self.left == other.left && self.right == other.right
    }

    /// Get both term pairs for matching (for use in equality reasoning).
    /// Returns (forward, left, right) and (backward, right, left).
    pub fn both_term_pairs(&self) -> Vec<(bool, &ThinTerm, &ThinTerm)> {
        vec![
            (true, &self.left, &self.right),
            (false, &self.right, &self.left),
        ]
    }
}
