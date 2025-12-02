use serde::{Deserialize, Serialize};

use crate::kernel::atom::Atom;

/// A component of a ThinTerm in its flattened representation.
/// Either a Composite node or an Atom leaf node.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum ThinTermComponent {
    /// Indicates a composite argument with the given span (total number of components).
    /// The span includes this Composite marker itself, the head, and all arguments recursively.
    /// To skip over this entire subterm: index += span
    /// To enter this subterm (process the head): index += 1
    Composite { span: u16 },

    /// A leaf atom in the term tree.
    Atom(Atom),
}

/// A thin term stores term structure without type information.
/// Type information is stored separately in the TypeStore and SymbolTable.
/// The term is represented as a flat vector of components in pre-order traversal.
/// The first element is always the head atom, followed by the arguments.
///
/// Examples:
/// - Simple atom "a": [Atom(a)]
/// - Application "f(a)": [Atom(f), Atom(a)]
/// - Nested "f(a, g(b))": [Atom(f), Atom(a), Composite{span: 3}, Atom(g), Atom(b)]
///                                            ^--- this composite has span 3: the marker, g, and b
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct ThinTerm {
    components: Vec<ThinTermComponent>,
}

impl ThinTerm {
    /// Create a new ThinTerm from a vector of components.
    pub fn new(components: Vec<ThinTermComponent>) -> ThinTerm {
        ThinTerm { components }
    }

    /// Create a ThinTerm representing a single atom with no arguments.
    pub fn atom(atom: Atom) -> ThinTerm {
        ThinTerm {
            components: vec![ThinTermComponent::Atom(atom)],
        }
    }

    /// Get the components of this thin term.
    pub fn components(&self) -> &[ThinTermComponent] {
        &self.components
    }
}
