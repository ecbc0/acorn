use crate::simple_term::TypeId;

/// A flattened representation of a term that can include full type information.
/// In general, "size" in a region header tells you how much to increment to get to the next region.
pub enum FlatComponent {
    /// A TypedTerm indicates that the following regions of the buffer make up a term.
    /// The layout is:
    /// ... TypedTerm [type components] [value components] ...
    TypedTerm { size: u16 },

    /// A DataType is a single FlatComponent that represents a type.
    DataType(TypeId),

    /// The function type layout is:
    /// ... FunctionType [arg1] [arg2] ... [argn] [return-type]
    FunctionType { size: u16 },

    /// The generic type layout is:
    /// ... GenericType [param1] .. [paramn]
    GenericType { size: u16 },
}
