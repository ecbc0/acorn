use serde::{Deserialize, Serialize};

use crate::kernel::fat_term::TypeId;

/// A context stores type information for variables.
/// This is used with thin terms/literals/clauses to track variable types
/// without embedding them in the term structure itself.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub struct LocalContext {
    /// The types of variables, indexed by variable id.
    /// var_types[i] is the type of variable x_i.
    pub var_types: Vec<TypeId>,
}

use std::sync::LazyLock;

/// A static empty LocalContext for use when no context is needed.
static EMPTY_LOCAL_CONTEXT: LazyLock<LocalContext> = LazyLock::new(LocalContext::empty);

impl LocalContext {
    pub fn new(var_types: Vec<TypeId>) -> LocalContext {
        LocalContext { var_types }
    }

    pub fn empty() -> LocalContext {
        LocalContext { var_types: vec![] }
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

    /// Push a new variable type to the context.
    /// The variable ID will be the current length of the context.
    /// Returns the assigned variable ID.
    pub fn push_var_type(&mut self, type_id: TypeId) -> usize {
        let var_id = self.var_types.len();
        self.var_types.push(type_id);
        var_id
    }

    /// Set the type for a variable at a specific index.
    /// If the context is too short, it will be extended with EMPTY types.
    /// This is used when variable IDs are assigned externally (e.g., by next_var_id).
    pub fn set_var_type(&mut self, var_id: usize, type_id: TypeId) {
        use crate::kernel::fat_term::EMPTY;
        if var_id >= self.var_types.len() {
            self.var_types.resize(var_id + 1, EMPTY);
        }
        self.var_types[var_id] = type_id;
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
        use crate::kernel::fat_term::BOOL;
        static TEST_BOOL_CONTEXT: LazyLock<LocalContext> =
            LazyLock::new(|| LocalContext::new(vec![BOOL; 10]));
        &TEST_BOOL_CONTEXT
    }

    /// Returns a reference to a LocalContext with EMPTY types for tests.
    /// The context has 10 variables, all with type EMPTY (TypeId 0).
    /// This matches what FatTerm::parse creates.
    #[cfg(test)]
    pub fn test_empty_ref() -> &'static LocalContext {
        use crate::kernel::fat_term::EMPTY;
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
