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
