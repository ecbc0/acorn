use std::fmt;

use serde::{Deserialize, Serialize};

use super::atom::AtomId;
use super::types::GroundTypeId;

/// A Symbol represents named constants, functions, and primitive values in the environment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Symbol {
    // The boolean constant true.
    True,

    // The boolean constant false.
    False,

    // A ground type, used in ClosedType to represent types like Int, Bool, Type<CommRing>.
    // Ground types have no internal structure - they are atomic type constants.
    Type(GroundTypeId),

    // Synthetic atoms are created by the normalizer to handle expressions that cannot be converted
    // to CNF directly.
    // These don't have a name in the environment, so you need to create a definition before
    // generating code with them.
    Synthetic(AtomId),

    // Constant values that are accessible anywhere in the code.
    // This includes concepts like addition, zero, and the axioms.
    GlobalConstant(AtomId),

    // Constant values that are only accessible inside a particular block.
    ScopedConstant(AtomId),

    // Monomorphizations of polymorphic functions.
    // A monomorphization is when every parametric type has been replaced with a concrete type.
    Monomorph(AtomId),
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Symbol::True => write!(f, "true"),
            Symbol::False => write!(f, "false"),
            Symbol::Type(t) => write!(f, "T{}", t.as_u16()),
            Symbol::Synthetic(i) => write!(f, "s{}", i),
            Symbol::GlobalConstant(i) => write!(f, "g{}", i),
            Symbol::ScopedConstant(i) => write!(f, "c{}", i),
            Symbol::Monomorph(i) => write!(f, "m{}", i),
        }
    }
}
