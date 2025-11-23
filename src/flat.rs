use crate::term::TypeId;

/// A flattened representation of a term that can include full type information.
pub enum FlatComponent {
    /// A TermHeader indicates that the following regions of the buffer make up a term.
    /// The layout is:
    /// ... TermHeader [type components] [value components] ...
    TermHeader {
        num_type_components: u16,
        num_value_components: u16,
    },

    /// A DataType is a single FlatComponent that represents a type.
    DataType(TypeId),
}
