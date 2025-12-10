use std::collections::HashMap;

use crate::elaborator::acorn_type::AcornType;
use crate::elaborator::acorn_value::{AcornValue, ConstantInstance};
use crate::elaborator::names::ConstantName;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::closed_type::ClosedType;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Term;
use crate::kernel::type_store::TypeStore;

#[derive(Clone, Copy, Debug)]
pub enum NewConstantType {
    Global,
    Local,
}

/// In the Acorn language, constants and types have names, scoped by modules. They can be rich values
/// with internal structure, like polymorphic parameters or complex types.
/// The prover, on the other hand, operates in simply typed higher order logic.
/// The SymbolTable is a mapping between the two (excluding types, which are handled by TypeStore).
#[derive(Clone)]
pub struct SymbolTable {
    /// For global constant i in the prover, global_constants[i] is the corresponding ConstantName.
    /// Part of the Symbol -> ConstantName lookup direction.
    global_constants: Vec<Option<ConstantName>>,

    /// For global constant i in the prover, global_constant_types[i] is the type.
    global_constant_types: Vec<ClosedType>,

    /// For local constant i in the prover, scoped_constants[i] is the corresponding ConstantName.
    /// Part of the Symbol -> ConstantName lookup direction.
    scoped_constants: Vec<Option<ConstantName>>,

    /// For local constant i in the prover, scoped_constant_types[i] is the type.
    scoped_constant_types: Vec<ClosedType>,

    /// Inverse map of constants that can be referenced with a single name.
    /// The ConstantName -> Symbol lookup direction.
    name_to_symbol: HashMap<ConstantName, Symbol>,

    /// Maps the rich constant instance to the Symbol that represents it.
    /// The Symbol might be a Monomorph, or it might be an alias to another constant type.
    monomorph_to_symbol: HashMap<ConstantInstance, Symbol>,

    /// Indexed by the AtomId of the monomorph.
    /// For each id, store the rich constant corresponding to it.
    id_to_monomorph: Vec<ConstantInstance>,

    /// For monomorph i, monomorph_types[i] is the type.
    monomorph_types: Vec<ClosedType>,

    /// For synthetic atom i, synthetic_types[i] is the type.
    synthetic_types: Vec<ClosedType>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable {
            global_constants: vec![],
            global_constant_types: vec![],
            scoped_constants: vec![],
            scoped_constant_types: vec![],
            name_to_symbol: HashMap::new(),
            monomorph_to_symbol: HashMap::new(),
            id_to_monomorph: vec![],
            monomorph_types: vec![],
            synthetic_types: vec![],
        }
    }

    pub fn get_symbol(&self, name: &ConstantName) -> Option<Symbol> {
        if let ConstantName::Synthetic(i) = name {
            return Some(Symbol::Synthetic(*i));
        };
        self.name_to_symbol.get(name).cloned()
    }

    /// Get the closed type of a symbol.
    pub fn get_closed_type(&self, symbol: Symbol) -> &ClosedType {
        match symbol {
            Symbol::Synthetic(i) => &self.synthetic_types[i as usize],
            Symbol::GlobalConstant(i) => &self.global_constant_types[i as usize],
            Symbol::ScopedConstant(i) => &self.scoped_constant_types[i as usize],
            Symbol::Monomorph(i) => &self.monomorph_types[i as usize],
        }
    }

    /// Get the count of scoped constants for debugging.
    #[cfg(test)]
    pub fn scoped_constant_count(&self) -> usize {
        self.scoped_constant_types.len()
    }

    /// Declare a new synthetic atom with the given type.
    pub fn declare_synthetic(&mut self, closed_type: ClosedType) -> Symbol {
        let atom_id = self.synthetic_types.len() as AtomId;
        self.synthetic_types.push(closed_type);
        Symbol::Synthetic(atom_id)
    }

    /// Add a scoped constant with the given ClosedType, without a name.
    /// Returns the Symbol for the new constant.
    /// Primarily for testing with parsed terms like "c0", "c1".
    #[cfg(test)]
    pub fn add_scoped_constant(&mut self, closed_type: ClosedType) -> Symbol {
        let atom_id = self.scoped_constant_types.len() as AtomId;
        self.scoped_constants.push(None);
        self.scoped_constant_types.push(closed_type);
        Symbol::ScopedConstant(atom_id)
    }

    /// Add a global constant with the given ClosedType, without a name.
    /// Returns the Symbol for the new constant.
    /// Primarily for testing with parsed terms like "g0", "g1".
    #[cfg(test)]
    pub fn add_global_constant(&mut self, closed_type: ClosedType) -> Symbol {
        let atom_id = self.global_constant_types.len() as AtomId;
        self.global_constants.push(None);
        self.global_constant_types.push(closed_type);
        Symbol::GlobalConstant(atom_id)
    }

    /// Add a monomorph with the given ClosedType, without the full ConstantInstance.
    /// Returns the Symbol for the new monomorph.
    /// Primarily for testing with parsed terms like "m0", "m1".
    #[cfg(test)]
    pub fn add_monomorph(&mut self, closed_type: ClosedType) -> Symbol {
        let atom_id = self.monomorph_types.len() as AtomId;
        self.monomorph_types.push(closed_type);
        Symbol::Monomorph(atom_id)
    }

    /// Assigns an id to this (module, name) pair if it doesn't already have one.
    /// local determines whether the constant will be represented as a local or global symbol.
    pub fn add_constant(
        &mut self,
        name: ConstantName,
        ctype: NewConstantType,
        closed_type: ClosedType,
    ) -> Symbol {
        if name.is_synthetic() {
            panic!("synthetic atoms should not be stored in the ConstantMap");
        }
        if let Some(&symbol) = self.name_to_symbol.get(&name) {
            return symbol;
        }
        let symbol = match ctype {
            NewConstantType::Local => {
                let atom_id = self.scoped_constant_types.len() as AtomId;
                self.scoped_constants.push(Some(name.clone()));
                self.scoped_constant_types.push(closed_type);
                Symbol::ScopedConstant(atom_id)
            }
            NewConstantType::Global => {
                let atom_id = self.global_constant_types.len() as AtomId;
                self.global_constants.push(Some(name.clone()));
                self.global_constant_types.push(closed_type);
                Symbol::GlobalConstant(atom_id)
            }
        };
        self.name_to_symbol.insert(name, symbol);
        symbol
    }

    /// Add all constant names, monomorphs, and types from a value to the symbol table.
    /// This ensures that all constants and types in the value are registered.
    pub fn add_from(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
        type_store: &mut TypeStore,
    ) {
        // Add all types first, so they can be resolved to ClosedTypes
        value.for_each_type(&mut |t| {
            type_store.add_type(t);
        });

        // Now add all constants (types are now registered)
        value.for_each_constant(&mut |c| {
            if self.get_symbol(&c.name).is_none() {
                let closed_type = type_store
                    .get_closed_type(&c.instance_type)
                    .expect("type should be valid");
                self.add_constant(c.name.clone(), ctype, closed_type);
            }
            if !c.params.is_empty() {
                self.add_monomorph_instance(c, type_store);
            }
        });
    }

    /// Get the name corresponding to a particular global AtomId.
    pub fn name_for_global_id(&self, atom_id: AtomId) -> &ConstantName {
        &self.global_constants[atom_id as usize].as_ref().unwrap()
    }

    /// Get the name corresponding to a particular local AtomId.
    pub fn name_for_local_id(&self, atom_id: AtomId) -> &ConstantName {
        &self.scoped_constants[atom_id as usize].as_ref().unwrap()
    }

    /// Make this monomorphized constant an alias for the given name.
    /// If neither of the names map to anything, we create a new entry.
    /// This is rare but can happen if we're aliasing something that was structurally generated.
    pub fn alias_monomorph(
        &mut self,
        c: ConstantInstance,
        name: &ConstantName,
        constant_type: &AcornType,
        local: bool,
        type_store: &mut TypeStore,
    ) {
        // Register the type first so we can get its ClosedType
        type_store.add_type(constant_type);
        let closed_type = type_store
            .get_closed_type(constant_type)
            .expect("type should be valid");
        let ctype = if local {
            NewConstantType::Local
        } else {
            NewConstantType::Global
        };
        let symbol = self.add_constant(name.clone(), ctype, closed_type);
        self.monomorph_to_symbol.insert(c, symbol);
    }

    /// Should only be called when c has params.
    fn add_monomorph_instance(&mut self, c: &ConstantInstance, type_store: &mut TypeStore) {
        assert!(!c.params.is_empty());
        if self.monomorph_to_symbol.get(c).is_some() {
            // We already have it
            return;
        }

        // Construct a symbol and appropriate entries for this monomorph
        let closed_type = type_store
            .get_closed_type(&c.instance_type)
            .expect("type should be valid");
        let monomorph_id = self.monomorph_types.len() as AtomId;
        let symbol = Symbol::Monomorph(monomorph_id);
        self.id_to_monomorph.push(c.clone());
        self.monomorph_types.push(closed_type);
        self.monomorph_to_symbol.insert(c.clone(), symbol);
    }

    /// The monomorph should already have been added.
    pub fn term_from_monomorph(&self, c: &ConstantInstance) -> Result<Term, String> {
        if let Some(&symbol) = self.monomorph_to_symbol.get(&c) {
            Ok(Term::new(Atom::Symbol(symbol), vec![]))
        } else {
            Err(format!(
                "Monomorphized constant {} not found in symbol table",
                c
            ))
        }
    }

    pub fn get_monomorph(&self, id: AtomId) -> &ConstantInstance {
        &self.id_to_monomorph[id as usize]
    }
}
