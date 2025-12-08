use serde::{Deserialize, Serialize};

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
