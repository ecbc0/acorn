use std::collections::HashMap;

use crate::elaborator::acorn_type::AcornType;
use crate::elaborator::acorn_value::{AcornValue, ConstantInstance};
use crate::elaborator::names::ConstantName;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Term;
use crate::kernel::type_store::TypeStore;

#[derive(Clone, Copy, Debug)]
pub enum NewConstantType {
    Global,
    Local,
}

/// Info about a polymorphic constant's generic type structure.
/// Used to properly denormalize constants.
#[derive(Clone, Debug)]
pub struct PolymorphicInfo {
    /// The generic type with type Variables (not Arbitrary types).
    pub generic_type: AcornType,
    /// The ordered names of type parameters.
    pub type_param_names: Vec<String>,
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
    global_constant_types: Vec<Term>,

    /// For local constant i in the prover, scoped_constants[i] is the corresponding ConstantName.
    /// Part of the Symbol -> ConstantName lookup direction.
    scoped_constants: Vec<Option<ConstantName>>,

    /// For local constant i in the prover, scoped_constant_types[i] is the type.
    scoped_constant_types: Vec<Term>,

    /// Inverse map of constants that can be referenced with a single name.
    /// The ConstantName -> Symbol lookup direction.
    name_to_symbol: HashMap<ConstantName, Symbol>,

    /// Maps constant instances (with type parameters) to their Symbol aliases.
    /// Used for instance definitions where e.g. Arf.foo[Foo] = Foo.foo.
    instance_to_symbol: HashMap<ConstantInstance, Symbol>,

    /// For synthetic atom i, synthetic_types[i] is the type.
    synthetic_types: Vec<Term>,

    /// Maps polymorphic constant names to their generic type info.
    /// Used to properly denormalize constants.
    polymorphic_info: HashMap<ConstantName, PolymorphicInfo>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable {
            global_constants: vec![],
            global_constant_types: vec![],
            scoped_constants: vec![],
            scoped_constant_types: vec![],
            name_to_symbol: HashMap::new(),
            instance_to_symbol: HashMap::new(),
            synthetic_types: vec![],
            polymorphic_info: HashMap::new(),
        }
    }

    pub fn get_symbol(&self, name: &ConstantName) -> Option<Symbol> {
        if let ConstantName::Synthetic(i) = name {
            return Some(Symbol::Synthetic(*i));
        };
        self.name_to_symbol.get(name).cloned()
    }

    /// Get polymorphic info for a constant, if it's polymorphic.
    pub fn get_polymorphic_info(&self, name: &ConstantName) -> Option<&PolymorphicInfo> {
        self.polymorphic_info.get(name)
    }

    /// Get the type of a symbol.
    /// For Symbol::Type and built-in type symbols, this returns the Type kind (arity 0).
    /// Use get_symbol_type() with a TypeStore if you need proper kinds for type constructors.
    pub fn get_type(&self, symbol: Symbol) -> &Term {
        match symbol {
            Symbol::True | Symbol::False => Term::bool_type_ref(),
            Symbol::Empty | Symbol::Bool | Symbol::TypeSort | Symbol::Type(_) => {
                Term::type_sort_ref()
            }
            Symbol::Synthetic(i) => &self.synthetic_types[i as usize],
            Symbol::GlobalConstant(i) => &self.global_constant_types[i as usize],
            Symbol::ScopedConstant(i) => &self.scoped_constant_types[i as usize],
        }
    }

    /// Get the type of a symbol, with proper kinds for type symbols.
    /// For Symbol::Type, this returns the proper kind based on arity (e.g., Type -> Type for List).
    pub fn get_symbol_type(&self, symbol: Symbol, type_store: &TypeStore) -> Term {
        let result = match symbol {
            Symbol::True | Symbol::False => Term::bool_type(),
            Symbol::Empty | Symbol::Bool | Symbol::TypeSort => Term::type_sort(),
            Symbol::Type(ground_id) => type_store.get_type_kind(ground_id),
            Symbol::Synthetic(i) => self.synthetic_types[i as usize].clone(),
            Symbol::GlobalConstant(i) => self.global_constant_types[i as usize].clone(),
            Symbol::ScopedConstant(i) => self.scoped_constant_types[i as usize].clone(),
        };
        result.validate();
        result
    }

    /// Get the count of scoped constants for debugging.
    #[cfg(test)]
    pub fn scoped_constant_count(&self) -> usize {
        self.scoped_constant_types.len()
    }

    /// Get the number of scoped constants.
    #[cfg(test)]
    pub fn num_scoped_constants(&self) -> u32 {
        self.scoped_constant_types.len() as u32
    }

    /// Set the type for a scoped constant at a given index.
    #[cfg(test)]
    pub fn set_scoped_constant_type(&mut self, id: u32, var_type: Term) {
        self.scoped_constant_types[id as usize] = var_type;
    }

    /// Get the number of global constants.
    #[cfg(test)]
    pub fn num_global_constants(&self) -> u32 {
        self.global_constant_types.len() as u32
    }

    /// Set the type for a global constant at a given index.
    #[cfg(test)]
    pub fn set_global_constant_type(&mut self, id: u32, var_type: Term) {
        self.global_constant_types[id as usize] = var_type;
    }

    /// Get the number of synthetics.
    #[cfg(test)]
    pub fn num_synthetics(&self) -> u32 {
        self.synthetic_types.len() as u32
    }

    /// Set the type for a synthetic at a given index.
    #[cfg(test)]
    pub fn set_synthetic_type(&mut self, id: u32, var_type: Term) {
        self.synthetic_types[id as usize] = var_type;
    }

    /// Declare a new synthetic atom with the given type.
    pub fn declare_synthetic(&mut self, var_type: Term) -> Symbol {
        let atom_id = self.synthetic_types.len() as AtomId;
        self.synthetic_types.push(var_type);
        Symbol::Synthetic(atom_id)
    }

    /// Add a scoped constant with the given type, without a name.
    /// Returns the Symbol for the new constant.
    /// Primarily for testing with parsed terms like "c0", "c1".
    #[cfg(test)]
    pub fn add_scoped_constant(&mut self, var_type: Term) -> Symbol {
        let atom_id = self.scoped_constant_types.len() as AtomId;
        self.scoped_constants.push(None);
        self.scoped_constant_types.push(var_type);
        Symbol::ScopedConstant(atom_id)
    }

    /// Add a global constant with the given type, without a name.
    /// Returns the Symbol for the new constant.
    /// Primarily for testing with parsed terms like "g0", "g1".
    #[cfg(test)]
    pub fn add_global_constant(&mut self, var_type: Term) -> Symbol {
        let atom_id = self.global_constant_types.len() as AtomId;
        self.global_constants.push(None);
        self.global_constant_types.push(var_type);
        Symbol::GlobalConstant(atom_id)
    }

    /// Assigns an id to this (module, name) pair if it doesn't already have one.
    /// local determines whether the constant will be represented as a local or global symbol.
    pub fn add_constant(
        &mut self,
        name: ConstantName,
        ctype: NewConstantType,
        var_type: Term,
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
                self.scoped_constant_types.push(var_type);
                Symbol::ScopedConstant(atom_id)
            }
            NewConstantType::Global => {
                let atom_id = self.global_constant_types.len() as AtomId;
                self.global_constants.push(Some(name.clone()));
                self.global_constant_types.push(var_type);
                Symbol::GlobalConstant(atom_id)
            }
        };
        self.name_to_symbol.insert(name, symbol);
        symbol
    }

    /// Add all constant names, monomorphs, and types from a value to the symbol table.
    /// Polymorphic constants get Pi-wrapped types for dependent type representation.
    pub fn add_from(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
        type_store: &mut TypeStore,
    ) {
        use crate::elaborator::acorn_type::{AcornType, TypeParam};

        // Add all types first, so they can be resolved to type Terms
        value.for_each_type(&mut |t| {
            type_store.add_type(t);
        });

        // Now add all constants (types are now registered)
        value.for_each_constant(&mut |c| {
            if self.get_symbol(&c.name).is_none() {
                let is_polymorphic = !c.type_param_names.is_empty();
                let var_type = if !is_polymorphic {
                    // Non-polymorphic: use instance_type directly
                    type_store
                        .get_type_term(&c.instance_type)
                        .expect("type should be valid")
                } else {
                    // Polymorphic: use generic_type (which has Variable types) to compute
                    // the polymorphic type term. Create Variable params from type_param_names.
                    let variable_params: Vec<AcornType> = c
                        .type_param_names
                        .iter()
                        .map(|name| {
                            AcornType::Variable(TypeParam {
                                name: name.clone(),
                                typeclass: None,
                            })
                        })
                        .collect();

                    // Convert generic_type to a term with bound variables
                    let body_type =
                        type_store.to_polymorphic_type_term(&c.generic_type, &variable_params);

                    // Wrap in Pi(Type, ...) for each type parameter (from outermost to innermost)
                    let mut result = body_type;
                    for _ in (0..c.type_param_names.len()).rev() {
                        result = Term::pi(Term::type_sort(), result);
                    }
                    result
                };
                self.add_constant(c.name.clone(), ctype, var_type);

                // Store polymorphic info for later use in denormalization
                if is_polymorphic {
                    // Convert Arbitrary types to Variable types in generic_type
                    // The ConstantInstance we're visiting may have Arbitrary types,
                    // but we need Variable types for proper instantiation.
                    let params_for_genericize: Vec<TypeParam> = c
                        .type_param_names
                        .iter()
                        .map(|name| TypeParam {
                            name: name.clone(),
                            typeclass: None,
                        })
                        .collect();
                    let generic_type_with_variables =
                        c.generic_type.genericize(&params_for_genericize);

                    self.polymorphic_info.insert(
                        c.name.clone(),
                        PolymorphicInfo {
                            generic_type: generic_type_with_variables,
                            type_param_names: c.type_param_names.clone(),
                        },
                    );
                }
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

    /// Make this constant instance an alias for the given name.
    /// If neither of the names map to anything, we create a new entry.
    /// This is rare but can happen if we're aliasing something that was structurally generated.
    pub fn alias_instance(
        &mut self,
        c: ConstantInstance,
        name: &ConstantName,
        constant_type: &AcornType,
        local: bool,
        type_store: &mut TypeStore,
    ) {
        // Register the type first so we can get its type Term
        type_store.add_type(constant_type);
        let var_type = type_store
            .get_type_term(constant_type)
            .expect("type should be valid");
        let ctype = if local {
            NewConstantType::Local
        } else {
            NewConstantType::Global
        };
        let symbol = self.add_constant(name.clone(), ctype, var_type);
        self.instance_to_symbol.insert(c, symbol);
    }

    /// Build a term application for a polymorphic constant.
    /// E.g., for add[Int], builds add(Int) instead of using a monomorph symbol.
    /// However, if the constant has an alias (via alias_instance), use that instead.
    pub fn term_from_instance(
        &self,
        c: &ConstantInstance,
        type_store: &TypeStore,
    ) -> Result<Term, String> {
        self.term_from_instance_with_vars(c, type_store, None)
    }

    pub fn term_from_instance_with_vars(
        &self,
        c: &ConstantInstance,
        type_store: &TypeStore,
        type_var_map: Option<&HashMap<String, AtomId>>,
    ) -> Result<Term, String> {
        // Check for an alias first - instance definitions create aliases
        // where Arf.foo[Foo] = Foo.foo makes them the same symbol
        if let Some(&symbol) = self.instance_to_symbol.get(c) {
            return Ok(Term::atom(Atom::Symbol(symbol)));
        }

        // Get the base constant symbol
        let Some(base_symbol) = self.get_symbol(&c.name) else {
            return Err(format!("Base constant {} not found", c.name));
        };

        if c.params.is_empty() {
            // No type params, just return the base symbol
            return Ok(Term::atom(Atom::Symbol(base_symbol)));
        }

        // Convert type params to Terms
        let type_args: Vec<Term> = c
            .params
            .iter()
            .map(|param| type_store.to_type_term_with_vars(param, type_var_map))
            .collect();

        // Build application: base(type_arg1, type_arg2, ...)
        let head = Term::atom(Atom::Symbol(base_symbol));
        Ok(head.apply(&type_args))
    }
}
