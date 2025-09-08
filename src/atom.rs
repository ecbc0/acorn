use std::cmp::Ordering;
use std::fmt;

use serde::{Deserialize, Serialize};

pub type AtomId = u16;

/// Don't let skolem ids get this high.
/// We use ids in the invalid space for normalization purposes.
pub const INVALID_SKOLEM_ID: AtomId = 65000;

/// An atomic value does not have any internal structure.
/// The Atom is a lower-level representation.
/// It is used in the prover, but not in the AcornValue / Environment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Atom {
    True,

    // Constant values that are accessible anywhere in the code.
    // This includes concepts like addition, zero, and the axioms.
    GlobalConstant(AtomId),

    // Constant values that are only accessible inside a particular block.
    LocalConstant(AtomId),

    // Monomorphizations of polymorphic functions.
    // A monomorphization is when every parametric type has been replaced with a concrete type.
    Monomorph(AtomId),

    // A Variable can be a reference to a variable on the stack, or its meaning can be implicit,
    // depending on the context.
    // We drop the variable name. Instead we track an id.
    // This does mean that you must be careful when moving values between different environments.
    Variable(AtomId),

    // A skolem function or skolem constant is created by the normalizer to eliminate existential
    // clauses. It can't be referred to directly in code.
    Skolem(AtomId),
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Atom::True => write!(f, "true"),
            Atom::GlobalConstant(i) => write!(f, "g{}", i),
            Atom::LocalConstant(i) => write!(f, "c{}", i),
            Atom::Monomorph(i) => write!(f, "m{}", i),
            Atom::Variable(i) => write!(f, "x{}", i),
            Atom::Skolem(i) => write!(f, "s{}", i),
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
            'g' => Some(Atom::GlobalConstant(rest.parse().ok()?)),
            'c' => Some(Atom::LocalConstant(rest.parse().ok()?)),
            'x' => Some(Atom::Variable(rest.parse().ok()?)),
            'm' => Some(Atom::Monomorph(rest.parse().ok()?)),
            's' => Some(Atom::Skolem(rest.parse().ok()?)),
            _ => None,
        }
    }

    pub fn is_local_constant(&self) -> bool {
        match self {
            Atom::LocalConstant(_) => true,
            _ => false,
        }
    }

    pub fn is_variable(&self) -> bool {
        match self {
            Atom::Variable(_) => true,
            _ => false,
        }
    }

    // Orders two atoms, but considers all references the same, so that the ordering
    // is stable under variable renaming.
    pub fn stable_partial_order(&self, other: &Atom) -> Ordering {
        match (self, other) {
            (Atom::Variable(_), Atom::Variable(_)) => Ordering::Equal,
            (x, y) => x.cmp(y),
        }
    }

    /// Renumbers skolems from the provided list into the invalid range.
    pub fn invalidate_skolems(&self, from: &[AtomId]) -> Atom {
        match self {
            Atom::Skolem(i) => match from.iter().position(|x| x == i) {
                Some(j) => Atom::Skolem((INVALID_SKOLEM_ID as usize + j) as AtomId),
                None => *self,
            },
            a => *a,
        }
    }

    /// Replace the first `num_existential` variables with invalid skolems, renormalizing.
    pub fn instantiate_invalid_skolems(&self, num_existential: usize) -> Atom {
        match self {
            Atom::Variable(i) => {
                if (*i as usize) < num_existential {
                    Atom::Skolem((INVALID_SKOLEM_ID as usize + *i as usize) as AtomId)
                } else {
                    Atom::Variable(*i - num_existential as AtomId)
                }
            }
            a => *a,
        }
    }

    // Replaces x_i with x_{var_map[i]}.
    pub fn remap_variables(&self, var_map: &Vec<AtomId>) -> Atom {
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
        assert!(Atom::True < Atom::GlobalConstant(0));
        assert!(Atom::GlobalConstant(0) < Atom::GlobalConstant(1));
    }

    #[test]
    fn test_atom_stable_partial_ordering() {
        assert_eq!(
            Atom::GlobalConstant(0).stable_partial_order(&Atom::GlobalConstant(1)),
            Ordering::Less
        );
        assert_eq!(
            Atom::Variable(0).stable_partial_order(&Atom::Variable(1)),
            Ordering::Equal
        );
    }
}
