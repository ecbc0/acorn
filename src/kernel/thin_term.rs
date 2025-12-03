use serde::{Deserialize, Serialize};

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::context::Context;
use crate::kernel::fat_term::TypeId;
use crate::kernel::symbol_table::SymbolTable;
use crate::kernel::type_store::TypeStore;

/// A component of a ThinTerm in its flattened representation.
/// Either a Composite node or an Atom leaf node.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum ThinTermComponent {
    /// Indicates a composite argument with the given span (total number of components).
    /// The span includes this Composite marker itself, the head, and all arguments recursively.
    /// To skip over this entire subterm: index += span
    /// To enter this subterm (process the head): index += 1
    Composite { span: u16 },

    /// A leaf atom in the term tree.
    Atom(Atom),
}

/// A thin term stores term structure without type information.
/// Type information is stored separately in the TypeStore and SymbolTable.
/// The term is represented as a flat vector of components in pre-order traversal.
/// The first element is always the head atom, followed by the arguments.
///
/// Examples:
/// - Simple atom "a": [Atom(a)]
/// - Application "f(a)": [Atom(f), Atom(a)]
/// - Nested "f(a, g(b))": [Atom(f), Atom(a), Composite{span: 3}, Atom(g), Atom(b)]
///                                            ^--- this composite has span 3: the marker, g, and b
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct ThinTerm {
    components: Vec<ThinTermComponent>,
}

impl ThinTerm {
    /// Create a new ThinTerm from a vector of components.
    pub fn new(components: Vec<ThinTermComponent>) -> ThinTerm {
        ThinTerm { components }
    }

    /// Create a ThinTerm representing a single atom with no arguments.
    pub fn atom(atom: Atom) -> ThinTerm {
        ThinTerm {
            components: vec![ThinTermComponent::Atom(atom)],
        }
    }

    /// Get the components of this thin term.
    pub fn components(&self) -> &[ThinTermComponent] {
        &self.components
    }

    /// Get the head atom of this term.
    /// The head is always the first component (or first after Composite marker).
    pub fn get_head_atom(&self) -> &Atom {
        match &self.components[0] {
            ThinTermComponent::Atom(atom) => atom,
            ThinTermComponent::Composite { .. } => {
                panic!("ThinTerm should not start with Composite marker")
            }
        }
    }

    /// Get the type of this term.
    /// Requires context to look up the type information.
    pub fn get_term_type(
        &self,
        _context: &Context,
        symbol_table: &SymbolTable,
        _type_store: &TypeStore,
    ) -> TypeId {
        // For a simple atom with no arguments, the term type equals the head type
        if self.is_atomic() {
            return self.get_head_type(symbol_table);
        }

        // For function applications, we need to compute the result type
        // This is a placeholder - full implementation needs type inference
        todo!("get_term_type for non-atomic terms requires type inference")
    }

    /// Get the type of the head atom.
    ///
    /// WARNING: This panics if the head is a variable. For variables, use Context::get_var_type() instead.
    /// This is a fundamental difference from FatTerm::get_head_type() which can return the type directly.
    pub fn get_head_type(&self, symbol_table: &SymbolTable) -> TypeId {
        let head = self.get_head_atom();
        match head {
            Atom::Variable(_) => {
                panic!("ThinTerm::get_head_type called on variable - use Context::get_var_type() instead")
            }
            Atom::Symbol(symbol) => symbol_table.get_type(*symbol),
            Atom::True => crate::kernel::fat_term::BOOL,
        }
    }

    /// Check if this term is atomic (no arguments).
    pub fn is_atomic(&self) -> bool {
        self.components.len() == 1
    }

    /// Check if this term is the boolean constant "true".
    pub fn is_true(&self) -> bool {
        matches!(self.get_head_atom(), Atom::True)
    }

    /// Check if this term is a variable (atomic and head is a variable).
    pub fn is_variable(&self) -> bool {
        self.is_atomic() && self.get_head_atom().is_variable()
    }

    /// If this is an atomic variable, return its index.
    pub fn atomic_variable(&self) -> Option<AtomId> {
        if !self.is_atomic() {
            return None;
        }
        match self.get_head_atom() {
            Atom::Variable(i) => Some(*i),
            _ => None,
        }
    }

    /// Check if this term contains a variable with the given index anywhere.
    pub fn has_variable(&self, index: AtomId) -> bool {
        for component in &self.components {
            if let ThinTermComponent::Atom(Atom::Variable(i)) = component {
                if *i == index {
                    return true;
                }
            }
        }
        false
    }

    /// Check if this term contains any variables.
    pub fn has_any_variable(&self) -> bool {
        for component in &self.components {
            if let ThinTermComponent::Atom(atom) = component {
                if atom.is_variable() {
                    return true;
                }
            }
        }
        false
    }

    /// Check if this term contains any local constants.
    pub fn has_scoped_constant(&self) -> bool {
        for component in &self.components {
            if let ThinTermComponent::Atom(atom) = component {
                if atom.is_scoped_constant() {
                    return true;
                }
            }
        }
        false
    }

    /// Check if this term contains any synthetic atoms.
    pub fn has_synthetic(&self) -> bool {
        use crate::kernel::symbol::Symbol;
        for component in &self.components {
            if let ThinTermComponent::Atom(Atom::Symbol(Symbol::Synthetic(_))) = component {
                return true;
            }
        }
        false
    }

    /// Count the number of atom components (excluding Composite markers).
    pub fn atom_count(&self) -> u32 {
        let mut count = 0;
        for component in &self.components {
            if let ThinTermComponent::Atom(Atom::True) = component {
                continue; // "true" counts as 0
            }
            if matches!(component, ThinTermComponent::Atom(_)) {
                count += 1;
            }
        }
        count
    }

    /// Get the number of arguments this term has.
    pub fn num_args(&self) -> usize {
        if self.components.len() <= 1 {
            return 0;
        }

        let mut arg_count = 0;
        let mut i = 1; // Skip the head
        while i < self.components.len() {
            arg_count += 1;
            if let ThinTermComponent::Composite { span } = self.components[i] {
                i += span as usize;
            } else {
                i += 1;
            }
        }
        arg_count
    }

    /// Iterate over all atoms in the term.
    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom> + '_ {
        self.components.iter().filter_map(|component| {
            if let ThinTermComponent::Atom(atom) = component {
                Some(atom)
            } else {
                None
            }
        })
    }

    /// Get the maximum variable index in this term, or None if there are no variables.
    pub fn max_variable(&self) -> Option<AtomId> {
        let mut max: Option<AtomId> = None;
        for atom in self.iter_atoms() {
            if let Atom::Variable(i) = atom {
                max = Some(match max {
                    None => *i,
                    Some(current_max) => current_max.max(*i),
                });
            }
        }
        max
    }

    /// Get the lowest variable number this term doesn't use.
    pub fn least_unused_variable(&self) -> AtomId {
        match self.max_variable() {
            Some(max) => max + 1,
            None => 0,
        }
    }

    /// Replace all occurrences of a variable with a term.
    ///
    /// WARNING: Current implementation is INCORRECT!
    /// When replacing variables, we need to:
    /// 1. Recursively process subterms (respecting Composite span markers)
    /// 2. Update span markers when the replacement changes the size
    /// 3. Handle the case where a variable is replaced with a complex term
    ///
    /// TODO: Implement proper recursive replacement with span adjustment.
    /// This is complex because we need to:
    /// - Track the size change when replacing a variable (1 component) with value (N components)
    /// - Update all parent Composite markers to reflect the new spans
    /// - Process subterms recursively
    pub fn replace_variable(&self, _id: AtomId, _value: &ThinTerm) -> ThinTerm {
        todo!(
            "ThinTerm::replace_variable needs proper implementation with span adjustment. \
             Current naive implementation breaks span invariants when replacing variables with complex terms."
        )
    }

    /// Replace an atom with another atom throughout the term.
    pub fn replace_atom(&self, old_atom: &Atom, new_atom: &Atom) -> ThinTerm {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                ThinTermComponent::Atom(atom) if atom == old_atom => {
                    ThinTermComponent::Atom(*new_atom)
                }
                c => *c,
            })
            .collect();
        ThinTerm::new(new_components)
    }

    /// Remap variables according to a mapping.
    /// Replaces x_i with x_{var_map[i]}.
    pub fn remap_variables(&self, var_map: &[AtomId]) -> ThinTerm {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                ThinTermComponent::Atom(atom) => {
                    ThinTermComponent::Atom(atom.remap_variables(var_map))
                }
                c => *c,
            })
            .collect();
        ThinTerm::new(new_components)
    }
}
