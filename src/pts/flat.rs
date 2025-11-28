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
/// Lambda, Pi,
pub enum FlatComponent {
    /// Note that a constant can represent any sort of thing: a value, a type, or a typeclass.
    Constant { constant_id: ConstantId },

    /// index is a de Bruijn index.
    /// Specifically, this means that the innermost is zero, and the number increments outwards.
    Variable { index: u32 },

    /// A "sort" is like a type but one step more generalized.
    Sort { sort: Sort },

    /// TODO: do we want a way to skip the whole term rooted here?
    Application { num_args: u8 },

    /// A lambda is a binder for one variable.
    Lambda { type_id: TypeId },

    /// TODO: describe what a "pi" is, in a way that I find coherent.
    /// A universally quantified binder? Eh?
    Pi { type_id: TypeId },
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

    /// Specific types are represented as Constants when they appear explicitly in the term.
    /// For example, these can be arguments to a typeclass.
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
        // Currently: ConstantId is 6 bytes, discriminant is 1 byte, padded to 8.
        assert_eq!(std::mem::size_of::<FlatComponent>(), 8);
    }
}
