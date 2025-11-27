use crate::module::ModuleId;
use crate::simple_term::TypeId;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ConstantId {
    /// A constant defined locally, like within a single proof.
    /// Cannot be imported from other modules.
    Local { index: u16 },

    /// A constant explicitly defined in a model.
    /// (module_id, index) uniquely identifies the symbol.
    Module { module_id: ModuleId, index: u16 },

    /// A symbol created during elaboration or normalization.
    /// Can be used in certificates but not in explicit code.
    Synthetic { module_id: ModuleId, index: u16 },
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

pub enum FlatComponent {
    /// index is a de Bruijn index.
    /// Specifically, this means that the innermost is zero, and the number increments outwards.
    Variable { index: u32 },

    /// Note that a constant can represent either a type or a value.
    /// TODO: how are types represented, with the ConstantId?
    Constant { constant_id: ConstantId },

    /// A "sort" is like a type but one step more generalized.
    Sort { sort: Sort },

    /// A lambda is a binder for one variable.
    Lambda { type_id: TypeId },

    /// TODO: describe what a "pi" is, in a way that I find coherent.
    /// A universally quantified binder? Eh?
    Pi { type_id: TypeId },

    /// TODO: do we want a way to skip the whole term rooted here?
    Application { num_args: u8 },
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
