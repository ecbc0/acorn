use serde::{Deserialize, Serialize};

use crate::kernel::fat_term::TypeId;

/// A context stores type information for variables.
/// This is used with thin terms/literals/clauses to track variable types
/// without embedding them in the term structure itself.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Context {
    /// The types of variables, indexed by variable id.
    /// var_types[i] is the type of variable x_i.
    pub var_types: Vec<TypeId>,
}

impl Context {
    pub fn new(var_types: Vec<TypeId>) -> Context {
        Context { var_types }
    }

    pub fn empty() -> Context {
        Context {
            var_types: vec![],
        }
    }

    /// Get the type of a variable by its id.
    pub fn get_var_type(&self, var_id: usize) -> Option<TypeId> {
        self.var_types.get(var_id).copied()
    }
}
