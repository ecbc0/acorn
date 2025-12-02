use std::cmp::Ordering;
use std::fmt;

use serde::{Deserialize, Serialize};

pub type AtomId = u16;

/// Don't let synthetic ids get this high.
/// We use ids in the invalid space for normalization purposes.
/// Bit of a hack.
pub const INVALID_SYNTHETIC_ID: AtomId = 65000;

/// A Symbol represents named constants and functions in the environment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Symbol {
    // Synthetic atoms are created by the normalizer to handle expressions that cannot be converted
    // to CNF directly.
    // These don't have a name in the environment, so you need to create a definition before
    // generating code with them.
    Synthetic(AtomId),

    // Constant values that are accessible anywhere in the code.
    // This includes concepts like addition, zero, and the axioms.
    GlobalConstant(AtomId),

    // Constant values that are only accessible inside a particular block.
    LocalConstant(AtomId),

    // Monomorphizations of polymorphic functions.
    // A monomorphization is when every parametric type has been replaced with a concrete type.
    Monomorph(AtomId),
}

/// An atomic value does not have any internal structure.
/// The Atom is a lower-level representation.
/// It is used in the prover, but not in the AcornValue / Environment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Atom {
    True,

    // A Variable can be a reference to a variable on the stack, or its meaning can be implicit,
    // depending on the context.
    // We drop the variable name. Instead we track an id.
    // This does mean that you must be careful when moving values between different environments.
    Variable(AtomId),

    // A symbol representing a constant or function.
    Symbol(Symbol),
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Symbol::Synthetic(i) => write!(f, "s{}", i),
            Symbol::GlobalConstant(i) => write!(f, "g{}", i),
            Symbol::LocalConstant(i) => write!(f, "c{}", i),
            Symbol::Monomorph(i) => write!(f, "m{}", i),
        }
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Atom::True => write!(f, "true"),
            Atom::Variable(i) => write!(f, "x{}", i),
            Atom::Symbol(s) => write!(f, "{}", s),
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
            'c' => Some(Atom::Symbol(Symbol::LocalConstant(rest.parse().ok()?))),
            'x' => Some(Atom::Variable(rest.parse().ok()?)),
            'm' => Some(Atom::Symbol(Symbol::Monomorph(rest.parse().ok()?))),
            's' => Some(Atom::Symbol(Symbol::Synthetic(rest.parse().ok()?))),
            _ => None,
        }
    }

    pub fn is_local_constant(&self) -> bool {
        matches!(self, Atom::Symbol(Symbol::LocalConstant(_)))
    }

    pub fn is_variable(&self) -> bool {
        matches!(self, Atom::Variable(_))
    }

    // Orders two atoms, but considers all references the same, so that the ordering
    // is stable under variable renaming.
    pub fn stable_partial_order(&self, other: &Atom) -> Ordering {
        match (self, other) {
            (Atom::Variable(_), Atom::Variable(_)) => Ordering::Equal,
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

    /// Replace the first `num_to_replace` variables with invalid synthetic atoms, adjusting
    /// the subsequent variable ids accordingly.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> Atom {
        match self {
            Atom::Variable(i) => {
                if (*i as usize) < num_to_replace {
                    Atom::Symbol(Symbol::Synthetic(
                        (INVALID_SYNTHETIC_ID as usize + *i as usize) as AtomId,
                    ))
                } else {
                    Atom::Variable(*i - num_to_replace as AtomId)
                }
            }
            a => *a,
        }
    }

    // Replaces x_i with x_{var_map[i]}.
    pub fn remap_variables(&self, var_map: &[AtomId]) -> Atom {
        match self {
            Atom::Variable(i) => Atom::Variable(var_map[*i as usize]),
            a => *a,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atom_ordering() {
        assert!(Atom::True < Atom::Symbol(Symbol::GlobalConstant(0)));
        assert!(Atom::Symbol(Symbol::GlobalConstant(0)) < Atom::Symbol(Symbol::GlobalConstant(1)));
    }

    #[test]
    fn test_atom_stable_partial_ordering() {
        assert_eq!(
            Atom::Symbol(Symbol::GlobalConstant(0))
                .stable_partial_order(&Atom::Symbol(Symbol::GlobalConstant(1))),
            Ordering::Less
        );
        assert_eq!(
            Atom::Variable(0).stable_partial_order(&Atom::Variable(1)),
            Ordering::Equal
        );
    }

    #[test]
    fn test_atom_size() {
        // Atom should be small since it's used extensively in the prover.
        // AtomId is u16 (2 bytes), plus 1 byte for the enum discriminant = 4 bytes total
        // (with alignment padding).
        assert_eq!(std::mem::size_of::<Atom>(), 4);
    }
}
