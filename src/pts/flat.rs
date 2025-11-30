use crate::module::ModuleId;
use crate::simple_term::TypeId;

/// Values, types, and typeclasses in Acorn can all be represented as terms in a "pure type system".
/// See:
///   https://en.wikipedia.org/wiki/Pure_type_system
///
/// A term is logically a tree. For efficiency, we use a flattened representation,
/// so that a term can be a &[FlatComponent].
///
/// Variable, Constant, and Sort are leaves in the tree.
/// Application, Lambda, and Pi are internal nodes in the tree.
///
/// In the flat representation, nodes are immediately followed by their children.
pub enum FlatComponent {
    /// Note that a constant can represent any sort of thing: a value, a type, or a typeclass.
    Constant { constant_id: ConstantId },

    /// index is a de Bruijn index.
    /// Specifically, this means that the innermost is zero, and the number increments outwards.
    Variable { index: u16 },

    /// A "sort" is like a type but one step more generalized.
    Sort { sort: Sort },

    /// The first child of an Application node is the function that's being applied.
    Application {
        /// How many arguments there are. Must be positive.
        num_args: u16,

        /// How many components are in the tree rooted here.
        num_components: u16,
    },

    /// A lambda is a binder for one variable.
    /// It has two children. The first is the type, the second is the body.
    Lambda {
        /// index is the de Bruijn index for the variable bound here.
        /// This isn't strictly necessary but it seems simpler to include it.
        index: u16,

        /// How many components are in the tree rooted here.
        num_components: u16,
    },

    /// A pi is a binder for one variable.
    /// It has two children. The first is the parameter type, the second is the result type.
    Pi {
        /// index is the de Bruijn index for the variable bound here.
        /// This isn't strictly necessary but it seems simpler to include it.
        index: u16,

        /// How many components are in the tree rooted here.
        num_components: u16,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ConstantId {
    /// A value defined locally, like within a single proof.
    /// Cannot be imported from other modules.
    Local { index: u16 },

    /// A value explicitly defined in a module.
    /// (module_id, index) uniquely identifies the symbol.
    Global { index: u16 },

    /// A value created during elaboration or normalization.
    /// Can be used in certificates but not in explicit code.
    Synthetic { index: u16 },

    /// Ground types are represented as Constants when they appear explicitly in the term.
    Type { type_id: TypeId },

    /// Typeclasses have the module in which they were originally defined.
    Typeclass {
        module_id: ModuleId,
        typeclass_id: u16,
    },
}

/// Acorn doesn't support a hierarchy of universes yet. Just three levels.
pub enum Sort {
    /// The Acorn language itself doesn't expose props to the user, but internally we can represent them.
    Prop,

    /// Your typical "Acorn Type" that is defined with "structure" or "inductive".
    Type,

    /// Typeclasses that are defined with the "typeclass" keyword.
    Typeclass,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_flat_component_size() {
        // This test ensures we don't accidentally grow FlatComponent.
        // If you need to increase this, make sure it's intentional.
        // ConstantId is 6 bytes. Rust uses niche optimization to fit
        // FlatComponent's discriminant into unused ConstantId discriminant values.
        assert_eq!(std::mem::size_of::<FlatComponent>(), 6);
    }
}
