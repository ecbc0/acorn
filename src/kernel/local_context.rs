use serde::{Deserialize, Serialize};

use crate::kernel::atom::AtomId;
use crate::kernel::term::Term;
use crate::kernel::types::TypeclassId;

/// A context stores type information for variables.
/// This is used with terms/literals/clauses to track variable types
/// without embedding them in the term structure itself.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LocalContext {
    /// The types of variables, indexed by variable id.
    /// var_types[i] is the type (as a Term) for variable x_i.
    var_types: Vec<Term>,
}

use std::sync::LazyLock;

/// A static empty LocalContext for use when no context is needed.
static EMPTY_LOCAL_CONTEXT: LazyLock<LocalContext> = LazyLock::new(LocalContext::empty);

impl LocalContext {
    pub fn empty() -> LocalContext {
        LocalContext { var_types: vec![] }
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
        let var_types: Vec<Term> = var_ids
            .iter()
            .map(|&id| {
                self.get_var_type(id as usize).cloned().unwrap_or_else(|| {
                    panic!(
                        "LocalContext::remap: variable x{} not found (context has {} variables)",
                        id,
                        self.len()
                    )
                })
            })
            .collect();

        LocalContext { var_types }
    }

    /// Returns a reference to a static empty LocalContext.
    /// Use this when you need a &LocalContext but don't have actual variable types.
    pub fn empty_ref() -> &'static LocalContext {
        &EMPTY_LOCAL_CONTEXT
    }

    /// Get the type of a variable by its id.
    pub fn get_var_type(&self, var_id: usize) -> Option<&Term> {
        self.var_types.get(var_id)
    }

    /// Returns the typeclass constraint if the variable's type is a typeclass.
    /// When a type variable is constrained to a typeclass (e.g., `M: Monoid`),
    /// its type in the context is stored as `Atom::Typeclass(monoid_id)`.
    pub fn get_typeclass_constraint(&self, var_id: usize) -> Option<TypeclassId> {
        self.var_types
            .get(var_id)
            .and_then(|t| t.as_ref().as_typeclass())
    }

    /// Returns a slice of all variable types.
    pub fn get_var_types(&self) -> &[Term] {
        &self.var_types
    }

    /// Push a new type to the context.
    /// The variable ID will be the current length of the context.
    /// Returns the assigned variable ID.
    pub fn push_type(&mut self, var_type: Term) -> usize {
        let var_id = self.var_types.len();
        self.var_types.push(var_type);
        var_id
    }

    /// Set type for a variable at a specific index.
    /// If the context is too short, it will be extended with EMPTY placeholders.
    pub fn set_type(&mut self, var_id: usize, var_type: Term) {
        if var_id >= self.var_types.len() {
            // Extend with EMPTY placeholders for gap indices
            self.var_types.resize(var_id + 1, Term::empty_type());
        }
        self.var_types[var_id] = var_type;
    }

    /// Returns the number of variables in this context.
    pub fn len(&self) -> usize {
        self.var_types.len()
    }

    /// Returns true if this context has no variables.
    pub fn is_empty(&self) -> bool {
        self.var_types.is_empty()
    }

    /// Create a new LocalContext from types.
    pub fn from_types(var_types: Vec<Term>) -> LocalContext {
        LocalContext { var_types }
    }

    /// Validates that variable types only reference lower-numbered variables.
    ///
    /// For variable x_i, its type can only contain variables x_j where j < i.
    /// This ensures a well-founded ordering where type variables come before
    /// term variables that depend on them.
    ///
    /// Returns true if all variable types satisfy this constraint.
    pub fn validate_variable_ordering(&self) -> bool {
        for (i, var_type) in self.var_types.iter().enumerate() {
            if let Some(max_var) = var_type.max_variable() {
                if max_var as usize >= i {
                    return false;
                }
            }
        }
        true
    }

    /// Validates that no variable has the Empty type.
    ///
    /// The Empty type is a placeholder that should never appear in a valid context.
    /// Having a variable with Empty type indicates an error in clause construction.
    ///
    /// Returns None if valid, or Some(var_id) for the first variable with Empty type.
    pub fn find_empty_type(&self) -> Option<usize> {
        for (i, var_type) in self.var_types.iter().enumerate() {
            if var_type.as_ref().is_empty_type() {
                return Some(i);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::types::GroundTypeId;

    fn ground(id: u16) -> Term {
        Term::ground_type(GroundTypeId::new(id))
    }

    #[test]
    fn test_remap_reorders_variables() {
        // Create a context with 3 variables of different types
        let ctx = LocalContext::from_types(vec![ground(0), ground(1), ground(2)]);

        // Remap to reorder: take vars [2, 0, 1]
        let remapped = ctx.remap(&[2, 0, 1]);

        assert_eq!(remapped.len(), 3);
        assert_eq!(remapped.get_var_type(0), Some(&ground(2)));
        assert_eq!(remapped.get_var_type(1), Some(&ground(0)));
        assert_eq!(remapped.get_var_type(2), Some(&ground(1)));
    }

    #[test]
    fn test_remap_subsets_variables() {
        // Create a context with 4 variables
        let ctx = LocalContext::from_types(vec![ground(0), ground(1), ground(2), ground(3)]);

        // Remap to take only vars [1, 3]
        let remapped = ctx.remap(&[1, 3]);

        assert_eq!(remapped.len(), 2);
        assert_eq!(remapped.get_var_type(0), Some(&ground(1)));
        assert_eq!(remapped.get_var_type(1), Some(&ground(3)));
    }

    #[test]
    fn test_remap_preserves_types() {
        // Create a context with a Pi type (function type)
        let pi_type = Term::pi(Term::bool_type(), Term::bool_type());
        let ground_type = Term::empty_type();

        let ctx = LocalContext::from_types(vec![ground_type.clone(), pi_type.clone()]);

        // Remap to reverse the order
        let remapped = ctx.remap(&[1, 0]);

        assert_eq!(remapped.len(), 2);
        // Check that types are preserved correctly
        assert_eq!(remapped.get_var_type(0), Some(&pi_type));
        assert_eq!(remapped.get_var_type(1), Some(&ground_type));
    }

    #[test]
    fn test_remap_empty() {
        let ctx = LocalContext::from_types(vec![Term::bool_type(), Term::empty_type()]);

        // Remap to empty
        let remapped = ctx.remap(&[]);

        assert_eq!(remapped.len(), 0);
    }

    #[test]
    fn test_remap_duplicates_variable() {
        // It's valid to include the same variable ID multiple times
        let ctx = LocalContext::from_types(vec![Term::bool_type(), Term::empty_type()]);

        let remapped = ctx.remap(&[0, 0, 1, 0]);

        assert_eq!(remapped.len(), 4);
        assert_eq!(remapped.get_var_type(0), Some(&Term::bool_type()));
        assert_eq!(remapped.get_var_type(1), Some(&Term::bool_type()));
        assert_eq!(remapped.get_var_type(2), Some(&Term::empty_type()));
        assert_eq!(remapped.get_var_type(3), Some(&Term::bool_type()));
    }

    #[test]
    #[should_panic(expected = "variable x5 not found")]
    fn test_remap_panics_on_out_of_bounds() {
        let ctx = LocalContext::from_types(vec![Term::bool_type(), Term::empty_type()]);

        // Try to remap with an out-of-bounds variable ID
        ctx.remap(&[0, 5]);
    }

    #[test]
    fn test_validate_variable_ordering_valid() {
        use crate::kernel::atom::Atom;

        // Valid: x0 : Type (no variable references)
        let ctx1 = LocalContext::from_types(vec![Term::type_sort()]);
        assert!(ctx1.validate_variable_ordering());

        // Valid: x0 : Type, x1 : x0 (references lower-numbered variable)
        let type_type = Term::type_sort();
        let type_var_x0 = Term::atom(Atom::FreeVariable(0));
        let ctx2 = LocalContext::from_types(vec![type_type, type_var_x0]);
        assert!(ctx2.validate_variable_ordering());

        // Valid: x0 : Bool, x1 : Bool (no variable references in types)
        let ctx3 = LocalContext::from_types(vec![Term::bool_type(), Term::bool_type()]);
        assert!(ctx3.validate_variable_ordering());
    }

    #[test]
    fn test_validate_variable_ordering_invalid_self_reference() {
        use crate::kernel::atom::Atom;

        // Invalid: x0 : x0 (variable referencing itself)
        let type_var_x0 = Term::atom(Atom::FreeVariable(0));
        let ctx = LocalContext::from_types(vec![type_var_x0]);
        assert!(!ctx.validate_variable_ordering());
    }

    #[test]
    fn test_validate_variable_ordering_invalid_forward_reference() {
        use crate::kernel::atom::Atom;

        // Invalid: x0 : x1, x1 : Type (x0 references higher-numbered x1)
        let type_type = Term::type_sort();
        let type_var_x1 = Term::atom(Atom::FreeVariable(1));
        let ctx = LocalContext::from_types(vec![type_var_x1, type_type]);
        assert!(!ctx.validate_variable_ordering());
    }

    #[test]
    fn test_validate_variable_ordering_nested_reference() {
        use crate::kernel::atom::Atom;

        // Setup: need a type constructor like List
        // For this test, we'll use a Pi type: x0 : Type, x1 : x0 -> x0

        let type_type = Term::type_sort();
        let type_var_x0 = Term::atom(Atom::FreeVariable(0));
        let arrow_type = Term::pi(type_var_x0.clone(), type_var_x0.clone()); // x0 -> x0

        // Valid: x0 : Type, x1 : x0 -> x0
        let ctx = LocalContext::from_types(vec![type_type, arrow_type]);
        assert!(ctx.validate_variable_ordering());
    }

    #[test]
    fn test_get_typeclass_constraint() {
        use crate::kernel::types::TypeclassId;

        // Create a context with a typeclass-constrained type variable
        let monoid_id = TypeclassId::new(0);
        let typeclass_type = Term::typeclass(monoid_id);
        let ctx = LocalContext::from_types(vec![typeclass_type, Term::bool_type()]);

        // x0 has typeclass constraint
        assert_eq!(ctx.get_typeclass_constraint(0), Some(monoid_id));

        // x1 has no typeclass constraint (it's Bool, not a typeclass)
        assert_eq!(ctx.get_typeclass_constraint(1), None);

        // x2 doesn't exist
        assert_eq!(ctx.get_typeclass_constraint(2), None);
    }
}
