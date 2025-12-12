use serde::{Deserialize, Serialize};
use std::fmt;

use crate::kernel::atom::Atom;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Term;
use crate::kernel::types::GroundTypeId;

// Note: Atom and Symbol are still used in the ground() constructor

/// A closed type representation - a type with no free variables.
///
/// ClosedType is a newtype wrapper around Term, used for storing types in the KernelContext.
/// Unlike general Terms which are for "open terms" with free variables, ClosedType represents
/// fully-resolved types that may contain Pi (dependent function types).
///
/// Examples:
/// - Simple ground type: `Bool`
/// - Arrow type: `A -> B` (represented as Pi)
/// - Type application: `List[Int]` (represented as Application)
///
/// Note: Within ClosedType, variables represent de Bruijn indices for bound variables
/// introduced by Pi, not free variables.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Serialize, Deserialize)]
pub struct ClosedType(Term);

impl ClosedType {
    /// Create a ClosedType representing a ground type.
    /// Takes a GroundTypeId to ensure only ground types are wrapped.
    pub fn ground(type_id: GroundTypeId) -> ClosedType {
        ClosedType(Term::atom(Atom::Symbol(Symbol::Type(type_id))))
    }

    /// Returns a ClosedType for the Bool type.
    pub fn bool() -> ClosedType {
        ClosedType::ground(GroundTypeId::new(1))
    }

    /// Returns a static reference to the Bool type.
    pub fn bool_ref() -> &'static ClosedType {
        use std::sync::LazyLock;
        static BOOL_TYPE: LazyLock<ClosedType> = LazyLock::new(ClosedType::bool);
        &BOOL_TYPE
    }

    /// Returns a ClosedType for the Empty type.
    pub fn empty() -> ClosedType {
        ClosedType::ground(GroundTypeId::new(0))
    }

    /// Returns a static reference to the Empty type.
    pub fn empty_ref() -> &'static ClosedType {
        use std::sync::LazyLock;
        static EMPTY_TYPE: LazyLock<ClosedType> = LazyLock::new(ClosedType::empty);
        &EMPTY_TYPE
    }

    /// Create a ClosedType from a Term.
    /// Caller is responsible for ensuring the term represents a valid closed type.
    pub fn from_term(term: Term) -> ClosedType {
        ClosedType(term)
    }

    /// Get the underlying Term.
    pub fn as_term(&self) -> &Term {
        &self.0
    }

    /// Create a Pi type `(x : input) -> output`.
    /// For non-dependent arrow types, output simply doesn't reference `Atom::Variable(0)`.
    pub fn pi(input: ClosedType, output: ClosedType) -> ClosedType {
        ClosedType(Term::pi(input.0, output.0))
    }

    /// Create a type application like `List[Int]` or `Map[String, Int]`.
    /// `head` is the type constructor, `args` are the type parameters.
    pub fn application(head: ClosedType, args: Vec<ClosedType>) -> ClosedType {
        debug_assert!(
            !args.is_empty(),
            "application requires at least one argument"
        );
        let arg_terms: Vec<Term> = args.into_iter().map(|a| a.0).collect();
        ClosedType(Term::application_multi(head.0, arg_terms))
    }

    /// Returns true if this is a ground type (just a GroundTypeId).
    pub fn is_ground(&self) -> bool {
        self.0.as_ref().as_type_atom().is_some()
    }

    /// If this is a ground type, return its GroundTypeId.
    pub fn as_ground(&self) -> Option<GroundTypeId> {
        self.0.as_ref().as_type_atom()
    }

    /// Returns true if this is a Pi/arrow type.
    pub fn is_pi(&self) -> bool {
        self.0.as_ref().is_pi()
    }

    /// If this is a Pi type, return the input type and output type.
    pub fn as_pi(&self) -> Option<(ClosedType, ClosedType)> {
        match self.0.as_ref().split_pi() {
            Some((input, output)) => {
                Some((ClosedType(input.to_owned()), ClosedType(output.to_owned())))
            }
            None => None,
        }
    }

    /// Returns true if this is a type application (e.g., `List[Int]`).
    pub fn is_application(&self) -> bool {
        self.0.as_ref().is_application()
    }

    /// If this is a type application, returns (head, args).
    /// E.g., for `List[Int, Bool]`, returns `(List, [Int, Bool])`.
    pub fn as_application(&self) -> Option<(ClosedType, Vec<ClosedType>)> {
        self.0
            .as_ref()
            .split_application_multi()
            .map(|(head, args)| {
                let head = ClosedType::from_term(head);
                let args = args.into_iter().map(ClosedType::from_term).collect();
                (head, args)
            })
    }

    /// Apply a function type to get its codomain.
    /// Returns None if this is not a Pi type.
    /// Equivalent to TypeStore::apply_type() but works directly on ClosedType.
    pub fn apply(&self) -> Option<ClosedType> {
        self.as_pi().map(|(_, output)| output)
    }

    /// Format this closed type for display.
    fn format_impl(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(ground_id) = self.as_ground() {
            return write!(f, "T{}", ground_id);
        }
        if let Some((input, output)) = self.as_pi() {
            write!(f, "(")?;
            input.format_impl(f)?;
            write!(f, " -> ")?;
            output.format_impl(f)?;
            return write!(f, ")");
        }
        if let Some((head, args)) = self.as_application() {
            head.format_impl(f)?;
            write!(f, "[")?;
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                arg.format_impl(f)?;
            }
            return write!(f, "]");
        }
        // Fallback for unexpected cases
        write!(f, "{:?}", self.0)
    }
}

impl fmt::Display for ClosedType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.format_impl(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::types::{GROUND_BOOL, GROUND_EMPTY};

    #[test]
    fn test_closed_type_ground() {
        let ct = ClosedType::ground(GROUND_BOOL);
        assert!(ct.is_ground());
        assert_eq!(ct.as_ground(), Some(GROUND_BOOL));
        assert!(!ct.is_pi());
        assert_eq!(format!("{}", ct), "T1");
    }

    #[test]
    fn test_closed_type_pi() {
        let bool_type = ClosedType::ground(GROUND_BOOL);
        let empty_type = ClosedType::ground(GROUND_EMPTY);
        let pi_type = ClosedType::pi(bool_type.clone(), empty_type.clone());

        assert!(!pi_type.is_ground());
        assert!(pi_type.is_pi());

        let (input, output) = pi_type.as_pi().unwrap();
        assert_eq!(input.as_ground(), Some(GROUND_BOOL));
        assert_eq!(output.as_ground(), Some(GROUND_EMPTY));

        // Display should show (Bool -> Empty)
        assert_eq!(format!("{}", pi_type), "(T1 -> T0)");
    }

    #[test]
    fn test_closed_type_nested_pi() {
        // Bool -> Bool -> Bool
        let bool_type = ClosedType::ground(GROUND_BOOL);
        let inner = ClosedType::pi(bool_type.clone(), bool_type.clone());
        let outer = ClosedType::pi(bool_type.clone(), inner);

        assert!(outer.is_pi());
        let (input, output) = outer.as_pi().unwrap();
        assert_eq!(input.as_ground(), Some(GROUND_BOOL));
        assert!(output.is_pi());

        assert_eq!(format!("{}", outer), "(T1 -> (T1 -> T1))");
    }

    #[test]
    fn test_closed_type_application() {
        // Create List[Bool] using the application() constructor
        // We use GROUND_EMPTY as a stand-in for "List" type constructor
        let list_type = ClosedType::ground(GROUND_EMPTY);
        let bool_type = ClosedType::ground(GROUND_BOOL);
        let list_bool = ClosedType::application(list_type.clone(), vec![bool_type.clone()]);

        assert!(!list_bool.is_ground());
        assert!(!list_bool.is_pi());
        assert!(list_bool.is_application());
        assert_eq!(format!("{}", list_bool), "T0[T1]");

        // Test as_application
        let (head, args) = list_bool.as_application().unwrap();
        assert_eq!(head.as_ground(), Some(GROUND_EMPTY));
        assert_eq!(args.len(), 1);
        assert_eq!(args[0].as_ground(), Some(GROUND_BOOL));

        // Test with multiple args: Map[String, Int] (using GROUND_EMPTY and GROUND_BOOL as stand-ins)
        let map_type = ClosedType::ground(GROUND_EMPTY);
        let map_string_int =
            ClosedType::application(map_type, vec![bool_type.clone(), list_type.clone()]);
        assert!(map_string_int.is_application());

        let (head2, args2) = map_string_int.as_application().unwrap();
        assert_eq!(head2.as_ground(), Some(GROUND_EMPTY));
        assert_eq!(args2.len(), 2);
        assert_eq!(args2[0].as_ground(), Some(GROUND_BOOL));
        assert_eq!(args2[1].as_ground(), Some(GROUND_EMPTY));

        // Ground types are not applications
        assert!(!bool_type.is_application());
        assert!(bool_type.as_application().is_none());
    }

    #[test]
    fn test_closed_type_apply() {
        let bool_type = ClosedType::ground(GROUND_BOOL);
        let empty_type = ClosedType::ground(GROUND_EMPTY);

        // Ground types can't be applied
        assert!(bool_type.apply().is_none());

        // Pi type Bool -> Empty can be applied to get Empty
        let pi_type = ClosedType::pi(bool_type.clone(), empty_type.clone());
        let result = pi_type.apply().unwrap();
        assert_eq!(result.as_ground(), Some(GROUND_EMPTY));

        // Nested Pi type: Bool -> (Bool -> Empty)
        let inner_pi = ClosedType::pi(bool_type.clone(), empty_type.clone());
        let outer_pi = ClosedType::pi(bool_type.clone(), inner_pi);

        // First apply gives (Bool -> Empty)
        let after_first = outer_pi.apply().unwrap();
        assert!(after_first.is_pi());

        // Second apply gives Empty
        let after_second = after_first.apply().unwrap();
        assert_eq!(after_second.as_ground(), Some(GROUND_EMPTY));
    }
}
