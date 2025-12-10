use serde::{Deserialize, Serialize};
use std::fmt;

/// GroundTypeId for the Empty type.
pub const GROUND_EMPTY: GroundTypeId = GroundTypeId(0);
/// GroundTypeId for the Bool type.
pub const GROUND_BOOL: GroundTypeId = GroundTypeId(1);

/// A type ID that refers ONLY to a ground type (no internal structure).
/// Examples: Bool, Nat, Int, user-defined data types without parameters.
/// NOT for: function types, parameterized types like List[T].
///
/// This distinction is important because:
/// - `ClosedType::ground(GroundTypeId)` is always correct
/// - `Atom::Type(GroundTypeId)` ensures atoms only contain ground types
#[derive(
    Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize, Default,
)]
pub struct GroundTypeId(u16);

impl GroundTypeId {
    /// Create a new GroundTypeId.
    /// NOTE: This should generally only be called by TypeStore when registering ground types.
    pub const fn new(id: u16) -> GroundTypeId {
        GroundTypeId(id)
    }

    pub fn as_u16(self) -> u16 {
        self.0
    }
}

impl fmt::Display for GroundTypeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A typeclass identifier that uniquely identifies a typeclass in the type system.
#[derive(
    Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize, Default,
)]
pub struct TypeclassId(u16);

impl TypeclassId {
    pub const fn new(id: u16) -> TypeclassId {
        TypeclassId(id)
    }

    pub fn as_u16(self) -> u16 {
        self.0
    }
}

impl fmt::Display for TypeclassId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
