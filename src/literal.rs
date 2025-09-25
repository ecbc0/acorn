use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::fmt;

use crate::atom::{Atom, AtomId};
use crate::term::{Term, TypeId};

// Literals are always boolean-valued.
// In normalized form, left is the "larger" term.
// Literals like "foo(a, b, c)" are treated as equalities having both
// a left and a right side, by making a right side equal to the special constant "true".
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Literal {
    pub positive: bool,
    pub left: Term,
    pub right: Term,
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.positive {
            if self.is_boolean() {
                write!(f, "{}", self.left)
            } else {
                write!(f, "{} = {}", self.left, self.right)
            }
        } else if self.is_boolean() {
            write!(f, "not {}", self.left)
        } else {
            write!(f, "{} != {}", self.left, self.right)
        }
    }
}

fn needs_to_flip(left: &Term, right: &Term) -> bool {
    left.extended_kbo_cmp(right) == Ordering::Less
}

impl Literal {
    // Normalizes the direction.
    // The larger term should be on the left of the literal.
    pub fn new(positive: bool, left: Term, right: Term) -> Literal {
        let (lit, _) = Literal::new_with_flip(positive, left, right);
        lit
    }

    // Normalizes the direction.
    // The larger term should be on the left of the literal.
    // Returns the literal and whether it was flipped.
    pub fn new_with_flip(positive: bool, left: Term, right: Term) -> (Literal, bool) {
        if needs_to_flip(&left, &right) {
            (
                Literal {
                    positive,
                    left: right,
                    right: left,
                },
                true,
            )
        } else {
            (
                Literal {
                    positive,
                    left,
                    right,
                },
                false,
            )
        }
    }

    pub fn validate(&self) {
        if Literal::new(self.positive, self.left.clone(), self.right.clone()) != *self {
            panic!("Literal is not normalized: {}", self);
        }
        self.validate_type();
    }

    pub fn from_signed_term(term: Term, positive: bool) -> Literal {
        Literal::new(positive, term, Term::new_true())
    }

    pub fn positive(term: Term) -> Literal {
        Literal::new(true, term, Term::new_true())
    }

    pub fn negative(term: Term) -> Literal {
        Literal::new(false, term, Term::new_true())
    }

    pub fn equals(left: Term, right: Term) -> Literal {
        Literal::new(true, left, right)
    }

    pub fn not_equals(left: Term, right: Term) -> Literal {
        Literal::new(false, left, right)
    }

    pub fn true_value() -> Literal {
        Literal::new(true, Term::new_true(), Term::new_true())
    }

    pub fn false_value() -> Literal {
        Literal::new(false, Term::new_true(), Term::new_true())
    }

    pub fn is_true_value(&self) -> bool {
        self.positive && self.left.is_true() && self.right.is_true()
    }

    pub fn is_false_value(&self) -> bool {
        !self.positive && self.left.is_true() && self.right.is_true()
    }

    pub fn negate(&self) -> Literal {
        Literal {
            positive: !self.positive,
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }

    /// Extracts the polarity from this literal, returning a positive version and the original polarity.
    /// If the literal is already positive, returns (self, true).
    /// If the literal is negative, returns (positive version, false).
    pub fn extract_polarity(&self) -> (Literal, bool) {
        if self.positive {
            (self.clone(), true)
        } else {
            (self.negate(), false)
        }
    }

    pub fn parse(s: &str) -> Literal {
        if s.contains(" != ") {
            let mut parts = s.split(" != ");
            let left = Term::parse(parts.next().unwrap());
            let right = Term::parse(parts.next().unwrap());
            Literal::not_equals(left, right)
        } else if s.contains(" = ") {
            let mut parts = s.split(" = ");
            let left = Term::parse(parts.next().unwrap());
            let right = Term::parse(parts.next().unwrap());
            Literal::equals(left, right)
        } else if s.starts_with("not ") {
            let term = Term::parse(&s[4..]);
            Literal::negative(term)
        } else {
            let term = Term::parse(s);
            Literal::positive(term)
        }
    }

    // Returns true if this literal is a tautology, i.e. foo = foo
    pub fn is_tautology(&self) -> bool {
        self.positive && self.left == self.right
    }

    // Returns whether this literal is syntactically impossible, i.e. foo != foo
    pub fn is_impossible(&self) -> bool {
        !self.positive && self.left == self.right
    }

    // Returns whether this literal is a boolean literal, i.e. "foo" or "!foo"
    pub fn is_boolean(&self) -> bool {
        self.right.is_true()
    }

    pub fn is_higher_order(&self) -> bool {
        self.left.is_higher_order() || self.right.is_higher_order()
    }

    pub fn var_type(&self, i: AtomId) -> Option<AtomId> {
        self.left.var_type(i).or_else(|| self.right.var_type(i))
    }

    // Deduplicates
    pub fn typed_atoms(&self) -> Vec<(TypeId, Atom)> {
        let mut answer = self.left.typed_atoms();
        answer.extend(self.right.typed_atoms());
        answer.sort();
        answer.dedup();
        answer
    }

    pub fn map(&self, f: &mut impl FnMut(&Term) -> Term) -> Literal {
        Literal::new(self.positive, f(&self.left), f(&self.right))
    }

    pub fn replace_atom(&self, atom: &Atom, replacement: &Atom) -> Literal {
        self.map(&mut |term| term.replace_atom(atom, replacement))
    }

    pub fn atom_count(&self) -> u32 {
        self.left.atom_count() + self.right.atom_count()
    }

    pub fn has_any_variable(&self) -> bool {
        self.left.has_any_variable() || self.right.has_any_variable()
    }

    pub fn has_any_applied_variable(&self) -> bool {
        self.left.has_any_applied_variable() || self.right.has_any_applied_variable()
    }

    pub fn has_local_constant(&self) -> bool {
        self.left.has_local_constant() || self.right.has_local_constant()
    }

    // Whether the components of this literal are strictly ordered according to the KBO.
    pub fn strict_kbo(&self) -> bool {
        match self.left.kbo_cmp(&self.right) {
            Ordering::Less => panic!("kbo inconsistency"),
            Ordering::Equal => false,
            Ordering::Greater => true,
        }
    }

    // Helper function to treat a literal as two terms.
    // For a literal s = t, get a vector with:
    // (true, s, t)
    // (false, t, s)
    pub fn both_term_pairs(&self) -> Vec<(bool, &Term, &Term)> {
        vec![
            (true, &self.left, &self.right),
            (false, &self.right, &self.left),
        ]
    }

    // Returns (right, left) with normalized var ids.
    pub fn normalized_reversed(&self) -> (Term, Term) {
        let mut var_ids = vec![];
        let mut right = self.right.clone();
        right.normalize_var_ids(&mut var_ids);
        let mut left = self.left.clone();
        left.normalize_var_ids(&mut var_ids);
        (right, left)
    }

    pub fn normalize_var_ids(&mut self, var_ids: &mut Vec<AtomId>) {
        self.left.normalize_var_ids(var_ids);
        self.right.normalize_var_ids(var_ids);
        if needs_to_flip(&self.left, &self.right) {
            self.flip();
        }
    }

    pub fn least_unused_variable(&self) -> AtomId {
        self.left
            .least_unused_variable()
            .max(self.right.least_unused_variable())
    }

    pub fn validate_type(&self) {
        if self.left.term_type != self.right.term_type {
            panic!(
                "Literal type mismatch: {} has type {} but {} has type {}",
                self.left, self.left.term_type, self.right, self.right.term_type
            );
        }
    }

    // An extension of the kbo ordering on literals.
    // Ignores sign.
    pub fn extended_kbo_cmp(&self, other: &Literal) -> Ordering {
        let left_cmp = self.left.extended_kbo_cmp(&other.left);
        if left_cmp != Ordering::Equal {
            return left_cmp;
        }
        self.right.extended_kbo_cmp(&other.right)
    }

    pub fn has_synthetic(&self) -> bool {
        self.left.has_synthetic() || self.right.has_synthetic()
    }

    // Whether either side of the literal has this as its head.
    pub fn has_head(&self, head: &Atom) -> bool {
        self.left.get_head_atom() == head || self.right.get_head_atom() == head
    }

    // Keep in mind this will denormalize the literal.
    pub fn flip(&mut self) {
        std::mem::swap(&mut self.left, &mut self.right);
    }

    // Return a new literal, along with whether we flipped this during normalization.
    pub fn replace_at_path(
        &self,
        left: bool,
        path: &[usize],
        new_subterm: Term,
    ) -> (Literal, bool) {
        let (u, v, flip1) = if left {
            (&self.left, &self.right, false)
        } else {
            (&self.right, &self.left, true)
        };
        let new_u = u.replace_at_path(path, new_subterm);
        let (new_literal, flip2) = Literal::new_with_flip(self.positive, new_u, v.clone());
        (new_literal, flip1 ^ flip2)
    }

    pub fn get_term_at_path(&self, left: bool, path: &[usize]) -> Option<&Term> {
        if left {
            self.left.get_term_at_path(path)
        } else {
            self.right.get_term_at_path(path)
        }
    }
}

// Literals are ordered so that you can normalize a clause by sorting its literals.
// This is using a traditional saturation-based ordering, which might not really make sense.
// Anyway.
// Negative literals come first. We depend on that in miscellaneous places.
// Then, we order backwards by term ordering for the left term.
// Then, backwards (I guess?) for the right term.
impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
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

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl Literal {
    /// Renumbers synthetic atoms from the provided list into the invalid range.
    /// This does renormalize, so it could be swapping the order.
    pub fn invalidate_synthetics(&self, from: &[AtomId]) -> Literal {
        let new_left = self.left.invalidate_synthetics(from);
        let new_right = self.right.invalidate_synthetics(from);
        Literal::new(self.positive, new_left, new_right)
    }

    /// Replace the first `num_to_replace` variables with invalid synthetic atoms, adjusting
    /// the subsequent variable ids accordingly.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> Literal {
        let new_left = self.left.instantiate_invalid_synthetics(num_to_replace);
        let new_right = self.right.instantiate_invalid_synthetics(num_to_replace);
        Literal::new(self.positive, new_left, new_right)
    }
}
