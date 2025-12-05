use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::fmt;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::thin_term::ThinTerm;
use crate::kernel::types::{TypeId, BOOL};

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
        let (lit, _) = ThinLiteral::new_with_flip(positive, left, right);
        lit
    }

    /// Create a positive literal from a single term (term = true).
    pub fn positive(term: ThinTerm) -> ThinLiteral {
        ThinLiteral::new(true, term, ThinTerm::atom(BOOL, Atom::True))
    }

    /// Create a negative literal from a single term (not term, i.e., term != true).
    pub fn negative(term: ThinTerm) -> ThinLiteral {
        ThinLiteral::new(false, term, ThinTerm::atom(BOOL, Atom::True))
    }

    /// Create an equality literal (left = right).
    pub fn equals(left: ThinTerm, right: ThinTerm) -> ThinLiteral {
        ThinLiteral::new(true, left, right)
    }

    /// Create an inequality literal (left != right).
    pub fn not_equals(left: ThinTerm, right: ThinTerm) -> ThinLiteral {
        ThinLiteral::new(false, left, right)
    }

    /// Parse a ThinLiteral from a string representation.
    /// Format: "left = right", "left != right", "not term", or just "term".
    pub fn parse(s: &str) -> ThinLiteral {
        if s.contains(" != ") {
            let mut parts = s.split(" != ");
            let left = ThinTerm::parse(parts.next().unwrap());
            let right = ThinTerm::parse(parts.next().unwrap());
            ThinLiteral::not_equals(left, right)
        } else if s.contains(" = ") {
            let mut parts = s.split(" = ");
            let left = ThinTerm::parse(parts.next().unwrap());
            let right = ThinTerm::parse(parts.next().unwrap());
            ThinLiteral::equals(left, right)
        } else if s.starts_with("not ") {
            let term = ThinTerm::parse(&s[4..]);
            ThinLiteral::negative(term)
        } else {
            let term = ThinTerm::parse(s);
            ThinLiteral::positive(term)
        }
    }

    /// Parse a ThinLiteral with context.
    /// The contexts are accepted but not used during parsing.
    pub fn parse_with_context(
        s: &str,
        _local_context: &LocalContext,
        _kernel_context: &KernelContext,
    ) -> ThinLiteral {
        ThinLiteral::parse(s)
    }

    /// Create a literal representing the value "true" (true = true).
    pub fn true_value() -> ThinLiteral {
        ThinLiteral::new(
            true,
            ThinTerm::atom(BOOL, Atom::True),
            ThinTerm::atom(BOOL, Atom::True),
        )
    }

    /// Create a literal representing the value "false" (true != true).
    pub fn false_value() -> ThinLiteral {
        ThinLiteral::new(
            false,
            ThinTerm::atom(BOOL, Atom::True),
            ThinTerm::atom(BOOL, Atom::True),
        )
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

    /// Check if this literal represents the value "true" (true = true).
    pub fn is_true_value(&self) -> bool {
        self.positive && self.left.is_true() && self.right.is_true()
    }

    /// Check if this literal represents the value "false" (true != true).
    pub fn is_false_value(&self) -> bool {
        !self.positive && self.left.is_true() && self.right.is_true()
    }

    /// Check if this literal contains any variables.
    pub fn has_any_variable(&self) -> bool {
        self.left.has_any_variable() || self.right.has_any_variable()
    }

    /// Check if this literal contains any local constants.
    pub fn has_scoped_constant(&self) -> bool {
        self.left.has_scoped_constant() || self.right.has_scoped_constant()
    }

    /// Check if this literal contains any synthetic atoms.
    pub fn has_synthetic(&self) -> bool {
        self.left.has_synthetic() || self.right.has_synthetic()
    }

    /// Count the total number of atoms in both terms.
    pub fn atom_count(&self) -> u32 {
        self.left.atom_count() + self.right.atom_count()
    }

    /// Get the type of a variable if it appears in this literal.
    pub fn var_type(&self, i: AtomId, context: &LocalContext) -> Option<TypeId> {
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

    /// Check if this literal is normalized.
    /// A literal is normalized if it doesn't need to flip its terms.
    /// The larger term (by KBO ordering) should be on the left.
    pub fn is_normalized(&self) -> bool {
        !needs_to_flip(&self.left, &self.right)
    }

    /// Flip the left and right terms of this literal.
    pub fn flip(&mut self) {
        std::mem::swap(&mut self.left, &mut self.right);
    }

    /// Normalize variable IDs in place so they appear in order of first occurrence.
    /// Returns true if the literal was flipped during normalization.
    pub fn normalize_var_ids(&mut self, var_ids: &mut Vec<AtomId>) -> bool {
        self.left.normalize_var_ids(var_ids);
        self.right.normalize_var_ids(var_ids);
        if needs_to_flip(&self.left, &self.right) {
            self.flip();
            true
        } else {
            false
        }
    }

    /// Normalize variable IDs in place so they appear in order of first occurrence,
    /// tracking the types of variables in the output.
    /// Returns true if the literal was flipped during normalization.
    pub fn normalize_var_ids_with_types(
        &mut self,
        var_ids: &mut Vec<AtomId>,
        var_types: &mut Vec<TypeId>,
        input_context: &LocalContext,
    ) -> bool {
        self.left
            .normalize_var_ids_with_types(var_ids, var_types, input_context);
        self.right
            .normalize_var_ids_with_types(var_ids, var_types, input_context);
        if needs_to_flip(&self.left, &self.right) {
            self.flip();
            true
        } else {
            false
        }
    }

    /// Normalizes the direction and returns whether it was flipped.
    /// The larger term should be on the left of the literal.
    pub fn new_with_flip(positive: bool, left: ThinTerm, right: ThinTerm) -> (ThinLiteral, bool) {
        if needs_to_flip(&left, &right) {
            (
                ThinLiteral {
                    positive,
                    left: right,
                    right: left,
                },
                true,
            )
        } else {
            (
                ThinLiteral {
                    positive,
                    left,
                    right,
                },
                false,
            )
        }
    }

    /// Create a literal from a term with a sign.
    pub fn from_signed_term(term: ThinTerm, positive: bool) -> ThinLiteral {
        ThinLiteral::new(positive, term, ThinTerm::new_true())
    }

    /// A higher order literal contains a higher order term.
    pub fn is_higher_order(&self) -> bool {
        self.left.is_higher_order() || self.right.is_higher_order()
    }

    /// Check if this literal contains any applied variables.
    pub fn has_any_applied_variable(&self) -> bool {
        self.left.has_any_applied_variable() || self.right.has_any_applied_variable()
    }

    /// Whether the components of this literal are strictly ordered according to the KBO.
    pub fn strict_kbo(&self) -> bool {
        match self.left.kbo_cmp(&self.right) {
            Ordering::Less => panic!("kbo inconsistency"),
            Ordering::Equal => false,
            Ordering::Greater => true,
        }
    }

    /// An extension of the kbo ordering on literals.
    /// Ignores sign.
    pub fn extended_kbo_cmp(&self, other: &ThinLiteral) -> Ordering {
        let left_cmp = self.left.extended_kbo_cmp(&other.left);
        if left_cmp != Ordering::Equal {
            return left_cmp;
        }
        self.right.extended_kbo_cmp(&other.right)
    }

    /// Returns (right, left, output_context) with normalized var ids.
    /// The output_context contains the types of the renumbered variables.
    /// The input_context provides the types of variables before renumbering.
    pub fn normalized_reversed(
        &self,
        input_context: &LocalContext,
    ) -> (ThinTerm, ThinTerm, LocalContext) {
        let mut var_ids: Vec<AtomId> = vec![];
        let mut var_types: Vec<TypeId> = vec![];
        let mut right = self.right.clone();
        right.normalize_var_ids_with_types(&mut var_ids, &mut var_types, input_context);
        let mut left = self.left.clone();
        left.normalize_var_ids_with_types(&mut var_ids, &mut var_types, input_context);
        let output_context = LocalContext::new(var_types);
        (right, left, output_context)
    }

    /// Deduplicates
    pub fn typed_atoms(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<(TypeId, Atom)> {
        let mut answer = self.left.typed_atoms(local_context, kernel_context);
        answer.extend(self.right.typed_atoms(local_context, kernel_context));
        answer.sort();
        answer.dedup();
        answer
    }

    /// Validate that both sides of the literal have the same type.
    pub fn validate_type(&self, local_context: &LocalContext, kernel_context: &KernelContext) {
        let left_type = self
            .left
            .get_term_type_with_context(local_context, kernel_context);
        let right_type = self
            .right
            .get_term_type_with_context(local_context, kernel_context);
        if left_type != right_type {
            panic!(
                "Literal type mismatch: {} has type {:?} but {} has type {:?}",
                self.left, left_type, self.right, right_type
            );
        }
    }

    /// Extracts the polarity from this literal, returning a positive version and the original polarity.
    /// If the literal is already positive, returns (self, true).
    /// If the literal is negative, returns (positive version, false).
    pub fn extract_polarity(&self) -> (ThinLiteral, bool) {
        if self.positive {
            (self.clone(), true)
        } else {
            (self.negate(), false)
        }
    }

    /// Whether either side of the literal has this as its head.
    pub fn has_head(&self, head: &Atom) -> bool {
        self.left.get_head_atom() == head || self.right.get_head_atom() == head
    }

    /// Renumbers synthetic atoms from the provided list into the invalid range.
    pub fn invalidate_synthetics(&self, from: &[AtomId]) -> ThinLiteral {
        let new_left = self.left.invalidate_synthetics(from);
        let new_right = self.right.invalidate_synthetics(from);
        let (lit, _) = ThinLiteral::new_with_flip(self.positive, new_left, new_right);
        lit
    }

    /// Replace the first `num_to_replace` variables with invalid synthetic atoms.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> ThinLiteral {
        let new_left = self.left.instantiate_invalid_synthetics(num_to_replace);
        let new_right = self.right.instantiate_invalid_synthetics(num_to_replace);
        let (lit, _) = ThinLiteral::new_with_flip(self.positive, new_left, new_right);
        lit
    }

    /// Get the subterm at the given path.
    /// If `left` is true, navigate into the left term, otherwise the right term.
    pub fn get_term_at_path(&self, left: bool, path: &[usize]) -> Option<ThinTerm> {
        if left {
            self.left.get_term_at_path(path)
        } else {
            self.right.get_term_at_path(path)
        }
    }

    /// Replace the subterm at the given path with a new term.
    /// If `left` is true, replace in the left term, otherwise the right term.
    /// Returns a new literal (may be flipped for normalization) and whether it was flipped.
    pub fn replace_at_path(
        &self,
        left: bool,
        path: &[usize],
        new_subterm: ThinTerm,
    ) -> (ThinLiteral, bool) {
        let (new_left, new_right) = if left {
            (
                self.left.replace_at_path(path, new_subterm),
                self.right.clone(),
            )
        } else {
            (
                self.left.clone(),
                self.right.replace_at_path(path, new_subterm),
            )
        };

        ThinLiteral::new_with_flip(self.positive, new_left, new_right)
    }
}

impl fmt::Display for ThinLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.positive {
            if self.is_signed_term() {
                write!(f, "{}", self.left)
            } else {
                write!(f, "{} = {}", self.left, self.right)
            }
        } else if self.is_signed_term() {
            write!(f, "not {}", self.left)
        } else {
            write!(f, "{} != {}", self.left, self.right)
        }
    }
}

impl PartialOrd for ThinLiteral {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;

        let positive_cmp = self.positive.cmp(&other.positive);
        if positive_cmp != Ordering::Equal {
            return Some(positive_cmp);
        }

        let left_cmp = other.left.extended_kbo_cmp(&self.left);
        if left_cmp != Ordering::Equal {
            return Some(left_cmp);
        }

        Some(other.right.extended_kbo_cmp(&self.right))
    }
}

impl Ord for ThinLiteral {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Helper function to check if a literal needs to flip its terms.
/// Returns true if left < right in extended KBO ordering.
fn needs_to_flip(left: &ThinTerm, right: &ThinTerm) -> bool {
    use std::cmp::Ordering;
    left.extended_kbo_cmp(right) == Ordering::Less
}
