use serde::{Deserialize, Serialize};
use std::fmt;

use crate::kernel::atom::Atom;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::{Term, TermComponent, TermRef};
use crate::kernel::types::GroundTypeId;

/// A closed type representation - a type with no free variables.
///
/// ClosedType is a newtype wrapper around Term, used for storing types in the KernelContext.
/// Unlike general Terms which are for "open terms" with free variables, ClosedType represents
/// fully-resolved types that may contain Pi (dependent function types).
///
/// The underlying Term uses the same `Vec<TermComponent>` format:
/// - Can contain `TermComponent::Pi { span }` for dependent function types
/// - Can contain `TermComponent::Application { span }` for type applications like `List[Int]`
/// - Can contain `Atom::Type(GroundTypeId)` for ground types like Int, Bool, Nat
/// - Cannot contain free variables (but can have bound variables from Pi)
///
/// Examples:
/// - Simple ground type: `[Atom(Type(BOOL))]` represents `Bool`
/// - Arrow type `A -> B`: `[Pi{span: 3}, Atom(Type(A)), Atom(Type(B))]`
/// - Type application `List[Int]`: `[Atom(Type(List)), Atom(Type(Int))]`
///
/// Note: Within ClosedType, `Atom::Variable` represents de Bruijn indices for bound variables
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

    /// Create a ClosedType from raw components.
    /// Caller is responsible for ensuring validity.
    pub fn from_components(components: Vec<TermComponent>) -> ClosedType {
        debug_assert!(!components.is_empty(), "ClosedType cannot be empty");
        ClosedType(Term::from_components(components))
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

    /// Get a TermRef to the underlying term.
    pub fn as_term_ref(&self) -> TermRef {
        self.0.as_ref()
    }

    /// Create a Pi type `(x : input) -> output`.
    /// For non-dependent arrow types, output simply doesn't reference `Atom::Variable(0)`.
    pub fn pi(input: ClosedType, output: ClosedType) -> ClosedType {
        ClosedType(Term::pi(input.0, output.0))
    }

    /// Returns true if this is a ground type (just a GroundTypeId).
    pub fn is_ground(&self) -> bool {
        let components = self.0.components();
        components.len() == 1
            && matches!(
                components[0],
                TermComponent::Atom(Atom::Symbol(Symbol::Type(_)))
            )
    }

    /// If this is a ground type, return its GroundTypeId.
    pub fn as_ground(&self) -> Option<GroundTypeId> {
        let components = self.0.components();
        if components.len() == 1 {
            if let TermComponent::Atom(Atom::Symbol(Symbol::Type(t))) = components[0] {
                return Some(t);
            }
        }
        None
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

    /// Returns the components slice for inspection.
    pub fn components(&self) -> &[TermComponent] {
        self.0.components()
    }

    /// Apply a function type to get its codomain.
    /// Returns None if this is not a Pi type.
    /// Equivalent to TypeStore::apply_type() but works directly on ClosedType.
    pub fn apply(&self) -> Option<ClosedType> {
        self.as_pi().map(|(_, output)| output)
    }

    fn format_at(&self, f: &mut fmt::Formatter, pos: usize) -> fmt::Result {
        let components = self.0.components();
        match &components[pos] {
            TermComponent::Pi { span: _ } => {
                let input_end = self.find_subterm_end(pos + 1);
                write!(f, "(")?;
                self.format_at(f, pos + 1)?;
                write!(f, " -> ")?;
                self.format_at(f, input_end)?;
                write!(f, ")")
            }
            TermComponent::Application { span } => {
                // Type application like List[Int]
                let span = *span as usize;
                // Format head
                self.format_at(f, pos + 1)?;
                write!(f, "[")?;
                // Format arguments
                let mut arg_pos = self.find_subterm_end(pos + 1);
                let mut first = true;
                while arg_pos < pos + span {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    self.format_at(f, arg_pos)?;
                    arg_pos = self.find_subterm_end(arg_pos);
                }
                write!(f, "]")
            }
            TermComponent::Atom(atom) => write!(f, "{}", atom),
        }
    }

    /// Find the end position of a subterm starting at `start`.
    fn find_subterm_end(&self, start: usize) -> usize {
        let components = self.0.components();
        match components[start] {
            TermComponent::Pi { span } | TermComponent::Application { span } => {
                start + span as usize
            }
            TermComponent::Atom(_) => start + 1,
        }
    }
}

impl fmt::Display for ClosedType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.format_at(f, 0)
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
        // Simulate List[Bool] - a type constructor applied to Bool
        // We use GROUND_EMPTY as a stand-in for "List" type constructor
        let list_bool = ClosedType::from_components(vec![
            TermComponent::Application { span: 3 },
            TermComponent::Atom(Atom::Symbol(Symbol::Type(GROUND_EMPTY))),
            TermComponent::Atom(Atom::Symbol(Symbol::Type(GROUND_BOOL))),
        ]);

        assert!(!list_bool.is_ground());
        assert!(!list_bool.is_pi());
        assert_eq!(format!("{}", list_bool), "T0[T1]");
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
