use std::cmp::Ordering;
use std::fmt;

use serde::{Deserialize, Serialize};

use super::symbol::Symbol;
use super::types::TypeclassId;

pub type AtomId = u16;

/// Don't let synthetic ids get this high.
/// We use ids in the invalid space for normalization purposes.
/// Bit of a hack.
pub const INVALID_SYNTHETIC_ID: AtomId = 65000;

/// An atomic value does not have any internal structure.
/// The Atom is a lower-level representation.
/// It is used in the prover, but not in the AcornValue / Environment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Atom {
    // A free variable used in clauses and unification.
    // These have unique IDs and their types are tracked in LocalContext.
    FreeVariable(AtomId),

    // A bound variable using de Bruijn indexing.
    // BoundVariable(0) refers to the closest enclosing Pi binder.
    // These only appear inside Pi output types and don't participate in unification.
    BoundVariable(u16),

    // A symbol representing a constant, function, type, or boolean.
    Symbol(Symbol),

    // A typeclass used as a type constraint for type variables.
    // When a type variable x has type Typeclass(Monoid), it means x is constrained to
    // types that implement Monoid.
    Typeclass(TypeclassId),
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Atom::FreeVariable(i) => write!(f, "x{}", i),
            Atom::BoundVariable(i) => write!(f, "b{}", i),
            Atom::Symbol(s) => write!(f, "{}", s),
            Atom::Typeclass(tc) => write!(f, "tc{}", tc.as_u16()),
        }
    }
}

impl Atom {
    pub fn new(s: &str) -> Atom {
        match Atom::parse(s) {
            Some(atom) => atom,
            None => panic!("failed to parse atom: '{}'", s),
        }
    }

    pub fn parse(s: &str) -> Option<Atom> {
        let mut chars = s.trim().chars();
        let first = chars.next()?;
        let rest = chars.as_str();
        match first {
            'g' => Some(Atom::Symbol(Symbol::GlobalConstant(rest.parse().ok()?))),
            'c' => Some(Atom::Symbol(Symbol::ScopedConstant(rest.parse().ok()?))),
            'x' => Some(Atom::FreeVariable(rest.parse().ok()?)),
            'b' => Some(Atom::BoundVariable(rest.parse().ok()?)),
            's' => Some(Atom::Symbol(Symbol::Synthetic(rest.parse().ok()?))),
            _ => None,
        }
    }

    pub fn is_scoped_constant(&self) -> bool {
        matches!(self, Atom::Symbol(Symbol::ScopedConstant(_)))
    }

    /// Returns true if this is a free variable (used in unification).
    pub fn is_free_variable(&self) -> bool {
        matches!(self, Atom::FreeVariable(_))
    }

    /// Returns true if this is a bound variable (de Bruijn index).
    pub fn is_bound_variable(&self) -> bool {
        matches!(self, Atom::BoundVariable(_))
    }

    /// Returns true if this is any kind of variable (free or bound).
    pub fn is_variable(&self) -> bool {
        matches!(self, Atom::FreeVariable(_) | Atom::BoundVariable(_))
    }

    /// Returns the TypeclassId if this is a Typeclass atom.
    pub fn as_typeclass(&self) -> Option<TypeclassId> {
        match self {
            Atom::Typeclass(id) => Some(*id),
            _ => None,
        }
    }

    // Orders two atoms, but considers all free variables the same, so that the ordering
    // is stable under variable renaming.
    // True and False always sort before other atoms to ensure literals have the expected orientation.
    pub fn stable_partial_order(&self, other: &Atom) -> Ordering {
        // Helper to check if an atom is a boolean constant (True or False)
        fn is_bool_constant(atom: &Atom) -> bool {
            matches!(
                atom,
                Atom::Symbol(Symbol::True) | Atom::Symbol(Symbol::False)
            )
        }

        match (self, other) {
            // All free variables are considered equal for stable ordering
            (Atom::FreeVariable(_), Atom::FreeVariable(_)) => Ordering::Equal,
            // Bound variables are compared by index (they're structural, not semantic)
            (Atom::BoundVariable(a), Atom::BoundVariable(b)) => a.cmp(b),
            // Bool constants sort before everything except other bool constants
            (a, b) if is_bool_constant(a) && is_bool_constant(b) => a.cmp(b),
            (a, _) if is_bool_constant(a) => Ordering::Less,
            (_, b) if is_bool_constant(b) => Ordering::Greater,
            (x, y) => x.cmp(y),
        }
    }

    /// Renumbers synthetic atoms from the provided list into the invalid range.
    pub fn invalidate_synthetics(&self, from: &[AtomId]) -> Atom {
        match self {
            Atom::Symbol(Symbol::Synthetic(i)) => match from.iter().position(|x| x == i) {
                Some(j) => Atom::Symbol(Symbol::Synthetic(
                    (INVALID_SYNTHETIC_ID as usize + j) as AtomId,
                )),
                None => *self,
            },
            a => *a,
        }
    }

    /// Replace the first `num_to_replace` free variables with invalid synthetic atoms, adjusting
    /// the subsequent variable ids accordingly.
    /// Bound variables are left unchanged.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> Atom {
        match self {
            Atom::FreeVariable(i) => {
                if (*i as usize) < num_to_replace {
                    Atom::Symbol(Symbol::Synthetic(
                        (INVALID_SYNTHETIC_ID as usize + *i as usize) as AtomId,
                    ))
                } else {
                    Atom::FreeVariable(*i - num_to_replace as AtomId)
                }
            }
            a => *a,
        }
    }

    // Replaces free variable x_i with x_{var_map[i]}.
    // Bound variables are left unchanged.
    pub fn remap_free_variables(&self, var_map: &[AtomId]) -> Atom {
        match self {
            Atom::FreeVariable(i) => Atom::FreeVariable(var_map[*i as usize]),
            a => *a,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atom_ordering() {
        assert!(Atom::Symbol(Symbol::True) < Atom::Symbol(Symbol::GlobalConstant(0)));
        assert!(Atom::Symbol(Symbol::GlobalConstant(0)) < Atom::Symbol(Symbol::GlobalConstant(1)));
    }

    #[test]
    fn test_atom_stable_partial_ordering() {
        assert_eq!(
            Atom::Symbol(Symbol::GlobalConstant(0))
                .stable_partial_order(&Atom::Symbol(Symbol::GlobalConstant(1))),
            Ordering::Less
        );
        // All free variables are equal for stable ordering
        assert_eq!(
            Atom::FreeVariable(0).stable_partial_order(&Atom::FreeVariable(1)),
            Ordering::Equal
        );
        // Bound variables compare by index
        assert_eq!(
            Atom::BoundVariable(0).stable_partial_order(&Atom::BoundVariable(1)),
            Ordering::Less
        );
    }

    #[test]
    fn test_atom_size() {
        // Atom should be small since it's used extensively in the prover.
        // All variants use u16, so size is 4 bytes (discriminant + u16 + padding).
        assert_eq!(std::mem::size_of::<Atom>(), 4);
    }
}
