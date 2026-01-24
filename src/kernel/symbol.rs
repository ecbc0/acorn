use std::fmt;

use serde::{Deserialize, Serialize};

use super::atom::AtomId;
use super::types::{GroundTypeId, TypeclassId};

/// A Symbol represents named constants, functions, and primitive values in the environment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Symbol {
    // The boolean constant true.
    True,

    // The boolean constant false.
    False,

    // The Empty type (bottom type).
    Empty,

    // The Bool type.
    Bool,

    // The type of types (kind *). Called "Type" in the language but "Type0" here
    // to distinguish from the Type(GroundTypeId) variant which is for user-defined types.
    Type0,

    // A ground type, used in type terms to represent user-defined types like Nat, Int, etc.
    // Ground types have no internal structure - they are atomic type constants.
    // Note: Empty, Bool, and Type0 are NOT GroundTypeIds - they have their own variants.
    Type(GroundTypeId),

    // A typeclass used as a type constraint for type variables.
    // When a type variable x has type Typeclass(Monoid), it means x is constrained to
    // types that implement Monoid.
    Typeclass(TypeclassId),

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
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Symbol::True => write!(f, "true"),
            Symbol::False => write!(f, "false"),
            Symbol::Empty => write!(f, "Empty"),
            Symbol::Bool => write!(f, "Bool"),
            Symbol::Type0 => write!(f, "Type0"),
            Symbol::Type(t) => write!(f, "T{}", t.as_u16()),
            Symbol::Typeclass(tc) => write!(f, "tc{}", tc.as_u16()),
            Symbol::Synthetic(i) => write!(f, "s{}", i),
            Symbol::GlobalConstant(i) => write!(f, "g{}", i),
            Symbol::ScopedConstant(i) => write!(f, "c{}", i),
        }
    }
}
