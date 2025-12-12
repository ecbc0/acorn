use serde::{Deserialize, Serialize};

use crate::kernel::atom::AtomId;
use crate::kernel::closed_type::ClosedType;

/// A context stores type information for variables.
/// This is used with terms/literals/clauses to track variable types
/// without embedding them in the term structure itself.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LocalContext {
    /// The closed types of variables, indexed by variable id.
    /// var_closed_types[i] is the ClosedType for variable x_i.
    var_closed_types: Vec<ClosedType>,
}

use std::sync::LazyLock;

/// A static empty LocalContext for use when no context is needed.
static EMPTY_LOCAL_CONTEXT: LazyLock<LocalContext> = LazyLock::new(LocalContext::empty);

impl LocalContext {
    pub fn empty() -> LocalContext {
        LocalContext {
            var_closed_types: vec![],
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
    /// # Panics
    /// Panics if any variable ID in `var_ids` is out of bounds for this context.
    pub fn remap(&self, var_ids: &[AtomId]) -> LocalContext {
        let var_closed_types: Vec<ClosedType> = var_ids
            .iter()
            .map(|&id| {
                self.get_var_closed_type(id as usize)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "LocalContext::remap: variable x{} not found (context has {} variables)",
                            id,
                            self.len()
                        )
                    })
            })
            .collect();

        LocalContext { var_closed_types }
    }

    /// Returns a reference to a static empty LocalContext.
    /// Use this when you need a &LocalContext but don't have actual variable types.
    pub fn empty_ref() -> &'static LocalContext {
        &EMPTY_LOCAL_CONTEXT
    }

    /// Get the closed type of a variable by its id.
    pub fn get_var_closed_type(&self, var_id: usize) -> Option<&ClosedType> {
        self.var_closed_types.get(var_id)
    }

    /// Returns a slice of all closed types.
    pub fn get_var_closed_types(&self) -> &[ClosedType] {
        &self.var_closed_types
    }

    /// Push a new ClosedType to the context.
    /// The variable ID will be the current length of the context.
    /// Returns the assigned variable ID.
    pub fn push_closed_type(&mut self, closed_type: ClosedType) -> usize {
        let var_id = self.var_closed_types.len();
        self.var_closed_types.push(closed_type);
        var_id
    }

    /// Set ClosedType for a variable at a specific index.
    /// If the context is too short, it will be extended with EMPTY placeholders.
    pub fn set_closed_type(&mut self, var_id: usize, closed_type: ClosedType) {
        use crate::kernel::types::EMPTY;
        if var_id >= self.var_closed_types.len() {
            // Extend with EMPTY placeholders for gap indices
            let empty_closed = ClosedType::ground(EMPTY);
            self.var_closed_types.resize(var_id + 1, empty_closed);
        }
        self.var_closed_types[var_id] = closed_type;
    }

    /// Returns the number of variables in this context.
    pub fn len(&self) -> usize {
        self.var_closed_types.len()
    }

    /// Returns true if this context has no variables.
    pub fn is_empty(&self) -> bool {
        self.var_closed_types.is_empty()
    }

    /// Create a new LocalContext from ClosedTypes only.
    pub fn from_closed_types(var_closed_types: Vec<ClosedType>) -> LocalContext {
        LocalContext { var_closed_types }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::closed_type::ClosedType;
    use crate::kernel::types::{GroundTypeId, BOOL, EMPTY};

    fn ground(id: u16) -> ClosedType {
        ClosedType::ground(GroundTypeId::new(id))
    }

    #[test]
    fn test_remap_reorders_variables() {
        // Create a context with 3 variables of different types
        let ctx = LocalContext::from_closed_types(vec![ground(0), ground(1), ground(2)]);

        // Remap to reorder: take vars [2, 0, 1]
        let remapped = ctx.remap(&[2, 0, 1]);

        assert_eq!(remapped.len(), 3);
        assert_eq!(remapped.get_var_closed_type(0), Some(&ground(2)));
        assert_eq!(remapped.get_var_closed_type(1), Some(&ground(0)));
        assert_eq!(remapped.get_var_closed_type(2), Some(&ground(1)));
    }

    #[test]
    fn test_remap_subsets_variables() {
        // Create a context with 4 variables
        let ctx = LocalContext::from_closed_types(vec![ground(0), ground(1), ground(2), ground(3)]);

        // Remap to take only vars [1, 3]
        let remapped = ctx.remap(&[1, 3]);

        assert_eq!(remapped.len(), 2);
        assert_eq!(remapped.get_var_closed_type(0), Some(&ground(1)));
        assert_eq!(remapped.get_var_closed_type(1), Some(&ground(3)));
    }

    #[test]
    fn test_remap_preserves_closed_types() {
        // Create a context with a Pi type (function type)
        let pi_type = ClosedType::pi(ClosedType::ground(BOOL), ClosedType::ground(BOOL));
        let ground_type = ClosedType::ground(EMPTY);

        let ctx = LocalContext::from_closed_types(vec![ground_type.clone(), pi_type.clone()]);

        // Remap to reverse the order
        let remapped = ctx.remap(&[1, 0]);

        assert_eq!(remapped.len(), 2);
        // Check that ClosedTypes are preserved correctly
        assert_eq!(remapped.get_var_closed_type(0), Some(&pi_type));
        assert_eq!(remapped.get_var_closed_type(1), Some(&ground_type));
    }

    #[test]
    fn test_remap_empty() {
        let ctx = LocalContext::from_closed_types(vec![ClosedType::bool(), ClosedType::empty()]);

        // Remap to empty
        let remapped = ctx.remap(&[]);

        assert_eq!(remapped.len(), 0);
    }

    #[test]
    fn test_remap_duplicates_variable() {
        // It's valid to include the same variable ID multiple times
        let ctx = LocalContext::from_closed_types(vec![ClosedType::bool(), ClosedType::empty()]);

        let remapped = ctx.remap(&[0, 0, 1, 0]);

        assert_eq!(remapped.len(), 4);
        assert_eq!(remapped.get_var_closed_type(0), Some(&ClosedType::bool()));
        assert_eq!(remapped.get_var_closed_type(1), Some(&ClosedType::bool()));
        assert_eq!(remapped.get_var_closed_type(2), Some(&ClosedType::empty()));
        assert_eq!(remapped.get_var_closed_type(3), Some(&ClosedType::bool()));
    }

    #[test]
    #[should_panic(expected = "variable x5 not found")]
    fn test_remap_panics_on_out_of_bounds() {
        let ctx = LocalContext::from_closed_types(vec![ClosedType::bool(), ClosedType::empty()]);

        // Try to remap with an out-of-bounds variable ID
        ctx.remap(&[0, 5]);
    }
}
