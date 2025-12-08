use serde::{Deserialize, Serialize};
use std::fmt;

use crate::kernel::atom::Atom;
use crate::kernel::term::TermComponent;
use crate::kernel::types::TypeId;

/// A closed type representation - a type with no free variables.
///
/// ClosedType is used for storing types in the KernelContext. Unlike Term which is for
/// "open terms" with free variables, ClosedType represents fully-resolved types that may
/// contain Pi (dependent function types).
///
/// The representation uses the same `Vec<TermComponent>` format as Term, but:
/// - Can contain `TermComponent::Pi { span }` for dependent function types
/// - Can contain `TermComponent::Application { span }` for type applications like `List[Int]`
/// - Can contain `Atom::Type(TypeId)` for ground types like Int, Bool, Nat
/// - Cannot contain free variables (but can have bound variables from Pi)
///
/// Examples:
/// - Simple ground type: `[Atom(Type(BOOL))]` represents `Bool`
/// - Arrow type `A -> B`: `[Pi{span: 3}, Atom(Type(A)), Atom(Type(B))]`
/// - Type application `List[Int]`: `[Atom(Type(List)), Atom(Type(Int))]`
///
/// Note: Within ClosedType, `Atom::Variable` represents de Bruijn indices for bound variables
/// introduced by Pi, not free variables.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct ClosedType {
    components: Vec<TermComponent>,
}

impl ClosedType {
    /// Create a ClosedType representing a ground type (TypeId).
    pub fn ground(type_id: TypeId) -> ClosedType {
        ClosedType {
            components: vec![TermComponent::Atom(Atom::Type(type_id))],
        }
    }

    /// Create a ClosedType from raw components.
    /// Caller is responsible for ensuring validity.
    pub fn from_components(components: Vec<TermComponent>) -> ClosedType {
        debug_assert!(!components.is_empty(), "ClosedType cannot be empty");
        ClosedType { components }
    }

    /// Create a Pi type `(x : input) -> output`.
    /// For non-dependent arrow types, output simply doesn't reference `Atom::Variable(0)`.
    pub fn pi(input: ClosedType, output: ClosedType) -> ClosedType {
        let span = 1 + input.components.len() + output.components.len();
        let mut components = vec![TermComponent::Pi { span: span as u16 }];
        components.extend(input.components);
        components.extend(output.components);
        ClosedType { components }
    }

    /// Returns true if this is a ground type (just a TypeId).
    pub fn is_ground(&self) -> bool {
        self.components.len() == 1
            && matches!(self.components[0], TermComponent::Atom(Atom::Type(_)))
    }

    /// If this is a ground type, return its TypeId.
    pub fn as_ground(&self) -> Option<TypeId> {
        if self.components.len() == 1 {
            if let TermComponent::Atom(Atom::Type(t)) = self.components[0] {
                return Some(t);
            }
        }
        None
    }

    /// Returns true if this is a Pi/arrow type.
    pub fn is_pi(&self) -> bool {
        matches!(self.components.first(), Some(TermComponent::Pi { .. }))
    }

    /// If this is a Pi type, return the input type and output type.
    pub fn as_pi(&self) -> Option<(ClosedType, ClosedType)> {
        if let Some(TermComponent::Pi { span }) = self.components.first() {
            let total_span = *span as usize;
            // Find where the input type ends
            // The input type starts at position 1
            let input_end = self.find_subterm_end(1);
            let input = ClosedType::from_components(self.components[1..input_end].to_vec());
            let output =
                ClosedType::from_components(self.components[input_end..total_span].to_vec());
            Some((input, output))
        } else {
            None
        }
    }

    /// Find the end position of a subterm starting at `start`.
    fn find_subterm_end(&self, start: usize) -> usize {
        match self.components[start] {
            TermComponent::Pi { span } | TermComponent::Application { span } => {
                start + span as usize
            }
            TermComponent::Atom(_) => start + 1,
        }
    }

    /// Returns the components slice for inspection.
    pub fn components(&self) -> &[TermComponent] {
        &self.components
    }

    fn format_at(&self, f: &mut fmt::Formatter, pos: usize) -> fmt::Result {
        match &self.components[pos] {
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
}

impl fmt::Display for ClosedType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.format_at(f, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::types::{BOOL, EMPTY};

    #[test]
    fn test_closed_type_ground() {
        let ct = ClosedType::ground(BOOL);
        assert!(ct.is_ground());
        assert_eq!(ct.as_ground(), Some(BOOL));
        assert!(!ct.is_pi());
        assert_eq!(format!("{}", ct), "T1");
    }

    #[test]
    fn test_closed_type_pi() {
        let bool_type = ClosedType::ground(BOOL);
        let empty_type = ClosedType::ground(EMPTY);
        let pi_type = ClosedType::pi(bool_type.clone(), empty_type.clone());

        assert!(!pi_type.is_ground());
        assert!(pi_type.is_pi());

        let (input, output) = pi_type.as_pi().unwrap();
        assert_eq!(input.as_ground(), Some(BOOL));
        assert_eq!(output.as_ground(), Some(EMPTY));

        // Display should show (Bool -> Empty)
        assert_eq!(format!("{}", pi_type), "(T1 -> T0)");
    }

    #[test]
    fn test_closed_type_nested_pi() {
        // Bool -> Bool -> Bool
        let bool_type = ClosedType::ground(BOOL);
        let inner = ClosedType::pi(bool_type.clone(), bool_type.clone());
        let outer = ClosedType::pi(bool_type.clone(), inner);

        assert!(outer.is_pi());
        let (input, output) = outer.as_pi().unwrap();
        assert_eq!(input.as_ground(), Some(BOOL));
        assert!(output.is_pi());

        assert_eq!(format!("{}", outer), "(T1 -> (T1 -> T1))");
    }

    #[test]
    fn test_closed_type_application() {
        // Simulate List[Bool] - a type constructor applied to Bool
        // We use EMPTY as a stand-in for "List" type constructor
        // Build List[Bool] manually: [Application{span:3}, Atom(EMPTY), Atom(BOOL)]
        let list_bool = ClosedType::from_components(vec![
            TermComponent::Application { span: 3 },
            TermComponent::Atom(Atom::Type(EMPTY)),
            TermComponent::Atom(Atom::Type(BOOL)),
        ]);

        assert!(!list_bool.is_ground());
        assert!(!list_bool.is_pi());
        assert_eq!(format!("{}", list_bool), "T0[T1]");
    }
}
