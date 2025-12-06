use serde::{Deserialize, Serialize};
use std::fmt;

/// A type identifier that uniquely identifies a type in the type system.
#[derive(
    Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize, Default,
)]
pub struct TypeId(u16);

impl TypeId {
    pub const fn new(id: u16) -> TypeId {
        TypeId(id)
    }

    pub fn as_u16(self) -> u16 {
        self.0
    }
}

impl fmt::Display for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub const EMPTY: TypeId = TypeId(0);
pub const BOOL: TypeId = TypeId(1);

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
