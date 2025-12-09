use serde::{Deserialize, Serialize};

use crate::kernel::atom::AtomId;
use crate::kernel::closed_type::ClosedType;
use crate::kernel::type_store::TypeStore;
use crate::kernel::types::TypeId;

/// A context stores type information for variables.
/// This is used with terms/literals/clauses to track variable types
/// without embedding them in the term structure itself.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct LocalContext {
    /// The types of variables, indexed by variable id.
    /// var_types[i] is the type of variable x_i.
    pub var_types: Vec<TypeId>,

    /// The closed types of variables, indexed by variable id.
    /// Parallel to var_types - var_closed_types[i] is the ClosedType for x_i.
    #[serde(skip)]
    var_closed_types: Vec<ClosedType>,
}

use std::sync::LazyLock;

/// A static empty LocalContext for use when no context is needed.
static EMPTY_LOCAL_CONTEXT: LazyLock<LocalContext> = LazyLock::new(LocalContext::empty);

impl LocalContext {
    /// Create a new LocalContext with the given variable types.
    /// Note: This creates ground ClosedTypes for each TypeId. If you need proper
    /// ClosedTypes, use new_with_type_store instead.
    pub fn new(var_types: Vec<TypeId>) -> LocalContext {
        let var_closed_types = var_types.iter().map(|&t| ClosedType::ground(t)).collect();
        LocalContext {
            var_types,
            var_closed_types,
        }
    }

    /// Create a new LocalContext with proper ClosedTypes computed from the TypeStore.
    pub fn new_with_type_store(var_types: Vec<TypeId>, type_store: &TypeStore) -> LocalContext {
        let var_closed_types = var_types
            .iter()
            .map(|&t| type_store.type_id_to_closed_type(t))
            .collect();
        LocalContext {
            var_types,
            var_closed_types,
        }
    }

    pub fn empty() -> LocalContext {
        LocalContext {
            var_types: vec![],
            var_closed_types: vec![],
        }
    }

    /// Create a new LocalContext from ClosedTypes directly.
    /// Note: This also populates var_types using the ground TypeId if available,
    /// or EMPTY as a placeholder for non-ground types.
    pub fn from_closed_types(var_closed_types: Vec<ClosedType>) -> LocalContext {
        use crate::kernel::types::EMPTY;
        let var_types = var_closed_types
            .iter()
            .map(|ct| ct.as_ground().unwrap_or(EMPTY))
            .collect();
        LocalContext {
            var_types,
            var_closed_types,
        }
    }

    /// Creates a new LocalContext by remapping variables from this context.
    ///
    /// `var_ids` specifies which original variable IDs to include in the new context.
    /// The new context will have variables numbered 0, 1, 2, ... corresponding to
    /// the original variable IDs in `var_ids`.
    ///
    /// For example, if `var_ids = [2, 0, 5]`, the new context will have:
    /// - New variable 0 with the type of original variable 2
    /// - New variable 1 with the type of original variable 0
    /// - New variable 2 with the type of original variable 5
    ///
    /// This preserves both TypeId and ClosedType information for each variable.
    ///
    /// # Panics
    /// Panics if any variable ID in `var_ids` is out of bounds for this context.
    pub fn remap(&self, var_ids: &[AtomId]) -> LocalContext {
        let var_types: Vec<TypeId> = var_ids
            .iter()
            .map(|&id| {
                self.get_var_type(id as usize).unwrap_or_else(|| {
                    panic!(
                        "LocalContext::remap: variable x{} not found (context has {} variables)",
                        id,
                        self.len()
                    )
                })
            })
            .collect();

        let var_closed_types: Vec<ClosedType> = var_ids
            .iter()
            .map(|&id| {
                self.get_var_closed_type(id as usize)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "LocalContext::remap: variable x{} closed type not found (context has {} variables)",
                            id,
                            self.len()
                        )
                    })
            })
            .collect();

        LocalContext {
            var_types,
            var_closed_types,
        }
    }

    /// Returns a reference to a static empty LocalContext.
    /// Use this when you need a &LocalContext but don't have actual variable types.
    pub fn empty_ref() -> &'static LocalContext {
        &EMPTY_LOCAL_CONTEXT
    }

    /// Get the type of a variable by its id.
    pub fn get_var_type(&self, var_id: usize) -> Option<TypeId> {
        self.var_types.get(var_id).copied()
    }

    /// Get the closed type of a variable by its id.
    pub fn get_var_closed_type(&self, var_id: usize) -> Option<&ClosedType> {
        self.var_closed_types.get(var_id)
    }

    /// Returns a slice of all closed types.
    pub fn get_var_closed_types(&self) -> &[ClosedType] {
        &self.var_closed_types
    }

    /// Push a new variable type to the context.
    /// The variable ID will be the current length of the context.
    /// Returns the assigned variable ID.
    /// Note: Uses ClosedType::ground() for the closed type. Use push_var_type_with_store
    /// for proper ClosedType conversion.
    pub fn push_var_type(&mut self, type_id: TypeId) -> usize {
        let var_id = self.var_types.len();
        self.var_types.push(type_id);
        self.var_closed_types.push(ClosedType::ground(type_id));
        var_id
    }

    /// Push a new variable type to the context with proper ClosedType from TypeStore.
    /// The variable ID will be the current length of the context.
    /// Returns the assigned variable ID.
    pub fn push_var_type_with_store(&mut self, type_id: TypeId, type_store: &TypeStore) -> usize {
        let var_id = self.var_types.len();
        self.var_types.push(type_id);
        self.var_closed_types
            .push(type_store.type_id_to_closed_type(type_id));
        var_id
    }

    /// Push a ClosedType directly to the context.
    /// The variable ID will be the current length of the context.
    /// Returns the assigned variable ID.
    /// Note: This also updates var_types using the ground TypeId if available,
    /// or EMPTY as a placeholder.
    pub fn push_closed_type(&mut self, closed_type: ClosedType) -> usize {
        use crate::kernel::types::EMPTY;
        let var_id = self.var_types.len();
        let type_id = closed_type.as_ground().unwrap_or(EMPTY);
        self.var_types.push(type_id);
        self.var_closed_types.push(closed_type);
        var_id
    }

    /// Set the type for a variable at a specific index.
    /// If the context is too short, it will be extended with EMPTY types.
    /// This is used when variable IDs are assigned externally (e.g., by next_var_id).
    /// Note: Uses ClosedType::ground() for the closed type. Use set_var_type_with_store
    /// for proper ClosedType conversion.
    pub fn set_var_type(&mut self, var_id: usize, type_id: TypeId) {
        use crate::kernel::types::EMPTY;
        if var_id >= self.var_types.len() {
            self.var_types.resize(var_id + 1, EMPTY);
            self.var_closed_types
                .resize(var_id + 1, ClosedType::ground(EMPTY));
        }
        self.var_types[var_id] = type_id;
        self.var_closed_types[var_id] = ClosedType::ground(type_id);
    }

    /// Set the type for a variable at a specific index with proper ClosedType from TypeStore.
    /// If the context is too short, it will be extended with EMPTY types.
    pub fn set_var_type_with_store(
        &mut self,
        var_id: usize,
        type_id: TypeId,
        type_store: &TypeStore,
    ) {
        use crate::kernel::types::EMPTY;
        if var_id >= self.var_types.len() {
            self.var_types.resize(var_id + 1, EMPTY);
            self.var_closed_types
                .resize(var_id + 1, ClosedType::ground(EMPTY));
        }
        self.var_types[var_id] = type_id;
        self.var_closed_types[var_id] = type_store.type_id_to_closed_type(type_id);
    }

    /// Set the ClosedType for a variable at a specific index.
    /// If the context is too short, it will be extended with EMPTY types.
    /// Note: This also updates var_types using the ground TypeId if available,
    /// or EMPTY as a placeholder.
    pub fn set_closed_type(&mut self, var_id: usize, closed_type: ClosedType) {
        use crate::kernel::types::EMPTY;
        if var_id >= self.var_types.len() {
            self.var_types.resize(var_id + 1, EMPTY);
            self.var_closed_types
                .resize(var_id + 1, ClosedType::ground(EMPTY));
        }
        let type_id = closed_type.as_ground().unwrap_or(EMPTY);
        self.var_types[var_id] = type_id;
        self.var_closed_types[var_id] = closed_type;
    }

    /// Returns the number of variables in this context.
    pub fn len(&self) -> usize {
        self.var_types.len()
    }

    /// Returns true if this context has no variables.
    pub fn is_empty(&self) -> bool {
        self.var_types.is_empty()
    }

    /// Returns a reference to a LocalContext with BOOL types for tests.
    /// The context has 10 variables, all with type BOOL (TypeId 1).
    #[cfg(test)]
    pub fn test_bool_ref() -> &'static LocalContext {
        use crate::kernel::types::BOOL;
        static TEST_BOOL_CONTEXT: LazyLock<LocalContext> =
            LazyLock::new(|| LocalContext::new(vec![BOOL; 10]));
        &TEST_BOOL_CONTEXT
    }

    /// Returns a reference to a LocalContext with EMPTY types for tests.
    /// The context has 10 variables, all with type EMPTY (TypeId 0).
    #[cfg(test)]
    pub fn test_empty_ref() -> &'static LocalContext {
        use crate::kernel::types::EMPTY;
        static TEST_EMPTY_CONTEXT: LazyLock<LocalContext> =
            LazyLock::new(|| LocalContext::new(vec![EMPTY; 10]));
        &TEST_EMPTY_CONTEXT
    }

    /// Creates a LocalContext with custom types for tests.
    #[cfg(test)]
    pub fn with_types(types: Vec<TypeId>) -> LocalContext {
        LocalContext::new(types)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::closed_type::ClosedType;
    use crate::kernel::types::{BOOL, EMPTY};

    #[test]
    fn test_remap_reorders_variables() {
        // Create a context with 3 variables of different types
        let ctx = LocalContext::new(vec![EMPTY, BOOL, TypeId::new(2)]);

        // Remap to reorder: take vars [2, 0, 1]
        let remapped = ctx.remap(&[2, 0, 1]);

        assert_eq!(remapped.len(), 3);
        assert_eq!(remapped.get_var_type(0), Some(TypeId::new(2)));
        assert_eq!(remapped.get_var_type(1), Some(EMPTY));
        assert_eq!(remapped.get_var_type(2), Some(BOOL));
    }

    #[test]
    fn test_remap_subsets_variables() {
        // Create a context with 4 variables
        let ctx = LocalContext::new(vec![EMPTY, BOOL, TypeId::new(2), TypeId::new(3)]);

        // Remap to take only vars [1, 3]
        let remapped = ctx.remap(&[1, 3]);

        assert_eq!(remapped.len(), 2);
        assert_eq!(remapped.get_var_type(0), Some(BOOL));
        assert_eq!(remapped.get_var_type(1), Some(TypeId::new(3)));
    }

    #[test]
    fn test_remap_preserves_closed_types() {
        // Create a context with a Pi type (function type)
        let pi_type = ClosedType::pi(ClosedType::ground(BOOL), ClosedType::ground(BOOL));
        let ground_type = ClosedType::ground(EMPTY);

        let ctx = LocalContext {
            var_types: vec![EMPTY, TypeId::new(2)],
            var_closed_types: vec![ground_type.clone(), pi_type.clone()],
        };

        // Remap to reverse the order
        let remapped = ctx.remap(&[1, 0]);

        assert_eq!(remapped.len(), 2);
        // Check that ClosedTypes are preserved correctly
        assert_eq!(remapped.get_var_closed_type(0), Some(&pi_type));
        assert_eq!(remapped.get_var_closed_type(1), Some(&ground_type));
    }

    #[test]
    fn test_remap_empty() {
        let ctx = LocalContext::new(vec![BOOL, EMPTY]);

        // Remap to empty
        let remapped = ctx.remap(&[]);

        assert_eq!(remapped.len(), 0);
    }

    #[test]
    fn test_remap_duplicates_variable() {
        // It's valid to include the same variable ID multiple times
        let ctx = LocalContext::new(vec![BOOL, EMPTY]);

        let remapped = ctx.remap(&[0, 0, 1, 0]);

        assert_eq!(remapped.len(), 4);
        assert_eq!(remapped.get_var_type(0), Some(BOOL));
        assert_eq!(remapped.get_var_type(1), Some(BOOL));
        assert_eq!(remapped.get_var_type(2), Some(EMPTY));
        assert_eq!(remapped.get_var_type(3), Some(BOOL));
    }

    #[test]
    #[should_panic(expected = "variable x5 not found")]
    fn test_remap_panics_on_out_of_bounds() {
        let ctx = LocalContext::new(vec![BOOL, EMPTY]);

        // Try to remap with an out-of-bounds variable ID
        ctx.remap(&[0, 5]);
    }
}
