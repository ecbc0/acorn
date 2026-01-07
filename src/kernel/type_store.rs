use std::collections::{HashMap, HashSet};

use crate::elaborator::acorn_type::{AcornType, Datatype, FunctionType, TypeParam, Typeclass};
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::term::Term;
use crate::kernel::types::{GroundTypeId, TypeclassId};

/// Manages ground type registration and typeclass relationships.
#[derive(Clone)]
pub struct TypeStore {
    /// ground_id_to_type[ground_id] is the AcornType for that ground type.
    /// Only ground types are stored here.
    ground_id_to_type: Vec<AcornType>,

    /// ground_id_to_arity[ground_id] is the number of type parameters for that type.
    /// For proper types like Bool, arity is 0.
    /// For type constructors like List, arity is 1.
    ground_id_to_arity: Vec<u8>,

    /// Maps Datatype (bare data type with no params) to its GroundTypeId.
    datatype_to_ground_id: HashMap<Datatype, GroundTypeId>,

    /// Maps Arbitrary type parameters to their GroundTypeId.
    arbitrary_to_ground_id: HashMap<TypeParam, GroundTypeId>,

    /// typeclass_to_id[typeclass] is the TypeclassId
    typeclass_to_id: HashMap<Typeclass, TypeclassId>,

    /// id_to_typeclass[typeclass_id] is the Typeclass
    id_to_typeclass: Vec<Typeclass>,

    /// typeclass_extends[typeclass_id] is the set of TypeclassIds that this typeclass extends.
    /// This is the transitive closure, so if A extends B and B extends C, then A's set contains both B and C.
    typeclass_extends: Vec<HashSet<TypeclassId>>,

    /// typeclass_instances[typeclass_id] is the set of GroundTypeIds that are instances of this typeclass.
    typeclass_instances: Vec<HashSet<GroundTypeId>>,
}

impl TypeStore {
    pub fn new() -> TypeStore {
        // Empty, Bool, and TypeSort are now Symbol variants, not GroundTypeIds.
        // No pre-registration needed.
        TypeStore {
            ground_id_to_type: vec![],
            ground_id_to_arity: vec![],
            datatype_to_ground_id: HashMap::new(),
            arbitrary_to_ground_id: HashMap::new(),
            typeclass_to_id: HashMap::new(),
            id_to_typeclass: vec![],
            typeclass_extends: vec![],
            typeclass_instances: vec![],
        }
    }

    /// Register a type in the type store. Call this before using to_type_term()
    /// to ensure ground types are registered.
    pub fn add_type(&mut self, acorn_type: &AcornType) {
        self.add_type_internal(acorn_type);
    }

    /// Internal implementation that registers ground types.
    /// Only user-defined ground types (bare Data types, Arbitrary) get GroundTypeIds.
    /// Empty, Bool, and TypeSort are Symbol variants, not GroundTypeIds.
    /// Non-ground types (Function, parameterized Data) are just recursively processed.
    fn add_type_internal(&mut self, acorn_type: &AcornType) {
        match acorn_type {
            // Empty and Bool are now Symbol variants, no registration needed
            AcornType::Empty | AcornType::Bool => {}

            // Bare data type: assign a new GroundTypeId
            AcornType::Data(datatype, params) if params.is_empty() => {
                if self.datatype_to_ground_id.contains_key(datatype) {
                    return; // Already registered
                }
                let ground_id = self.next_ground_id();
                self.ground_id_to_type.push(acorn_type.clone());
                self.ground_id_to_arity.push(0); // Default arity 0, will be updated by set_datatype_arity
                self.datatype_to_ground_id
                    .insert(datatype.clone(), ground_id);
            }

            // Parameterized data type: ensure bare constructor exists, then process params
            AcornType::Data(datatype, params) => {
                let bare_constructor = AcornType::Data(datatype.clone(), vec![]);
                self.add_type_internal(&bare_constructor);
                // Update arity if we see a parameterized version
                // This handles cases where we first see List (arity 0) then List[Int] (arity 1)
                let arity = params.len() as u8;
                if let Some(ground_id) = self.datatype_to_ground_id.get(datatype) {
                    let idx = ground_id.as_u16() as usize;
                    if idx < self.ground_id_to_arity.len() && self.ground_id_to_arity[idx] < arity {
                        self.ground_id_to_arity[idx] = arity;
                    }
                }
                for param in params {
                    self.add_type_internal(param);
                }
            }

            // Function type: recursively process component types (no GroundTypeId needed)
            AcornType::Function(ft) => {
                for arg_type in &ft.arg_types {
                    self.add_type_internal(arg_type);
                }
                self.add_type_internal(&ft.return_type);
            }

            // Arbitrary type: assign a new GroundTypeId
            AcornType::Arbitrary(type_param) => {
                if self.arbitrary_to_ground_id.contains_key(type_param) {
                    return; // Already registered
                }
                let ground_id = self.next_ground_id();
                self.ground_id_to_type.push(acorn_type.clone());
                self.ground_id_to_arity.push(0); // Arbitrary types have arity 0
                self.arbitrary_to_ground_id
                    .insert(type_param.clone(), ground_id);
            }

            // Variable types are represented as FreeVariable atoms, not registered as ground types.
            // They will be converted to FreeVariable by to_type_term_with_vars.
            AcornType::Variable(_) => {}
        }
    }

    /// Allocate the next GroundTypeId.
    fn next_ground_id(&self) -> GroundTypeId {
        GroundTypeId::new(self.ground_id_to_type.len() as u16)
    }

    /// Get the GroundTypeId for a bare Datatype (no type parameters).
    /// Returns None if the datatype hasn't been registered.
    pub fn get_datatype_id(&self, datatype: &Datatype) -> Option<GroundTypeId> {
        self.datatype_to_ground_id.get(datatype).copied()
    }

    /// Set the arity (number of type parameters) for a datatype.
    /// This should be called after the datatype is registered and its arity is known.
    pub fn set_datatype_arity(&mut self, datatype: &Datatype, arity: u8) {
        if let Some(ground_id) = self.datatype_to_ground_id.get(datatype) {
            let idx = ground_id.as_u16() as usize;
            if idx < self.ground_id_to_arity.len() {
                self.ground_id_to_arity[idx] = arity;
            }
        }
    }

    /// Get the arity (number of type parameters) for a ground type.
    pub fn get_arity(&self, ground_id: GroundTypeId) -> u8 {
        self.ground_id_to_arity
            .get(ground_id.as_u16() as usize)
            .copied()
            .unwrap_or(0)
    }

    /// Generate the kind Term for a type constructor with the given arity.
    /// arity 0 → Type
    /// arity 1 → Type -> Type (Pi from Type to Type)
    /// arity 2 → Type -> Type -> Type
    pub fn kind_for_arity(&self, arity: u8) -> Term {
        let type_term = Term::type_sort();
        let mut result = type_term.clone();
        for _ in 0..arity {
            result = Term::pi(type_term.clone(), result);
        }
        result
    }

    /// Get the kind (type) of a ground type.
    /// Proper types like Bool have kind Type.
    /// Type constructors like List (arity 1) have kind Type -> Type.
    pub fn get_type_kind(&self, ground_id: GroundTypeId) -> Term {
        let arity = self.get_arity(ground_id);
        self.kind_for_arity(arity)
    }

    /// Look up a GroundTypeId by datatype name string.
    /// Only works for types created by `KernelContext::add_datatype` (assumes ModuleId(0)).
    #[cfg(test)]
    pub fn get_ground_id_by_name(&self, name: &str) -> Option<GroundTypeId> {
        use crate::module::ModuleId;

        let datatype = Datatype {
            module_id: ModuleId(0),
            name: name.to_string(),
        };
        self.datatype_to_ground_id.get(&datatype).copied()
    }

    /// Get the type Term for an AcornType.
    /// Ground types must be registered first via add_type().
    pub fn get_type_term(&self, acorn_type: &AcornType) -> Result<Term, String> {
        Ok(self.to_type_term(acorn_type))
    }

    /// Convert an AcornType to a type Term.
    /// Only ground types (Bool, Empty, bare data types, arbitrary types) need to be registered.
    /// Function types and parameterized data types are constructed on the fly.
    ///
    /// If `type_var_map` is provided, type variables are converted to FreeVariable atoms
    /// using the mapping. This is used in polymorphic mode where type variables participate
    /// in unification like term variables.
    pub fn to_type_term_with_vars(
        &self,
        acorn_type: &AcornType,
        type_var_map: Option<&HashMap<String, AtomId>>,
    ) -> Term {
        match acorn_type {
            // Built-in types: use dedicated Symbol variants
            AcornType::Empty => Term::empty_type(),
            AcornType::Bool => Term::bool_type(),

            AcornType::Data(datatype, params) if params.is_empty() => {
                // Bare data type - use direct Datatype -> GroundTypeId lookup
                let ground_id = self
                    .datatype_to_ground_id
                    .get(datatype)
                    .unwrap_or_else(|| panic!("Data type {} not registered", datatype.name));
                Term::ground_type(*ground_id)
            }

            AcornType::Data(datatype, params) => {
                // Parameterized data type: build Application using Term::type_application()
                let constructor_ground = self
                    .datatype_to_ground_id
                    .get(datatype)
                    .unwrap_or_else(|| panic!("Data type {} not registered", datatype.name));
                let head = Term::ground_type(*constructor_ground);

                let args: Vec<Term> = params
                    .iter()
                    .map(|param| self.to_type_term_with_vars(param, type_var_map))
                    .collect();

                Term::type_application(head, args)
            }

            AcornType::Function(ft) => {
                // Function type: build nested Pi types (curried)
                let mut result = self.to_type_term_with_vars(&ft.return_type, type_var_map);

                // Build Pi types from right to left
                for arg_type in ft.arg_types.iter().rev() {
                    let arg_type_term = self.to_type_term_with_vars(arg_type, type_var_map);
                    result = Term::pi(arg_type_term, result);
                }

                result
            }

            AcornType::Variable(type_param) => {
                // Type variables become FreeVariable atoms if we have a mapping
                if let Some(map) = type_var_map {
                    if let Some(&var_id) = map.get(&type_param.name) {
                        return Term::atom(Atom::FreeVariable(var_id));
                    }
                }
                // Check if this is a synthesized variable name (like "x0", "x1")
                // created by type_term_to_acorn_type from a FreeVariable
                if type_param.name.starts_with('x') {
                    if let Ok(var_id) = type_param.name[1..].parse::<AtomId>() {
                        return Term::atom(Atom::FreeVariable(var_id));
                    }
                }
                // Check for BoundVariable-style names (like "T0", "T1")
                if type_param.name.starts_with('T') {
                    if let Ok(var_id) = type_param.name[1..].parse::<u16>() {
                        return Term::atom(Atom::BoundVariable(var_id));
                    }
                }
                panic!(
                    "Variable types should not be converted to type Term without binding context: {:?}. Use to_polymorphic_type_term or provide type_var_map.",
                    acorn_type
                );
            }

            AcornType::Arbitrary(type_param) => {
                // In polymorphic mode, check if this arbitrary type corresponds to a type parameter.
                // If so, convert it to a FreeVariable just like we do for Variable types.
                if let Some(map) = type_var_map {
                    if let Some(&var_id) = map.get(&type_param.name) {
                        return Term::atom(Atom::FreeVariable(var_id));
                    }
                }
                // Otherwise, use the registered ground type
                let ground_id = self
                    .arbitrary_to_ground_id
                    .get(type_param)
                    .unwrap_or_else(|| panic!("Arbitrary type {:?} not registered", type_param));
                Term::ground_type(*ground_id)
            }
        }
    }

    /// Convert an AcornType to a type Term (no type variable support).
    /// This is a convenience wrapper that panics on type variables.
    pub fn to_type_term(&self, acorn_type: &AcornType) -> Term {
        self.to_type_term_with_vars(acorn_type, None)
    }

    /// Convert an AcornType with type parameters to a type Term using bound variables.
    /// Type parameters in `params` are converted to BoundVariable(index) based on their position.
    /// For example, if params = [T, U] and the type is T -> U, we get Pi(b0, b1) where
    /// b0 = BoundVariable(0) and b1 = BoundVariable(1).
    /// The result should be wrapped in Pi(Type, ...) binders for each type parameter.
    pub fn to_polymorphic_type_term(&self, acorn_type: &AcornType, params: &[AcornType]) -> Term {
        self.to_polymorphic_type_term_impl(acorn_type, params)
    }

    fn to_polymorphic_type_term_impl(&self, acorn_type: &AcornType, params: &[AcornType]) -> Term {
        use crate::kernel::atom::Atom;

        match acorn_type {
            AcornType::Empty => Term::empty_type(),
            AcornType::Bool => Term::bool_type(),

            AcornType::Data(datatype, type_args) if type_args.is_empty() => {
                let ground_id = self
                    .datatype_to_ground_id
                    .get(datatype)
                    .unwrap_or_else(|| panic!("Data type {} not registered", datatype.name));
                Term::ground_type(*ground_id)
            }

            AcornType::Data(datatype, type_args) => {
                let constructor_ground = self
                    .datatype_to_ground_id
                    .get(datatype)
                    .unwrap_or_else(|| panic!("Data type {} not registered", datatype.name));
                let head = Term::ground_type(*constructor_ground);

                let args: Vec<Term> = type_args
                    .iter()
                    .map(|arg| self.to_polymorphic_type_term_impl(arg, params))
                    .collect();

                Term::type_application(head, args)
            }

            AcornType::Function(ft) => {
                let mut result = self.to_polymorphic_type_term_impl(&ft.return_type, params);

                // When wrapping with Pi, we need to shift bound variables in the result
                // because they're now inside a binder. Each Pi adds one to the De Bruijn index.
                for arg_type in ft.arg_types.iter().rev() {
                    let arg_type_term = self.to_polymorphic_type_term_impl(arg_type, params);
                    // Shift bound variables in result up by 1 since we're entering a Pi
                    result = result.shift_bound(0, 1);
                    result = Term::pi(arg_type_term, result);
                }

                result
            }

            AcornType::Variable(type_param) => {
                // Find the index of this type parameter in the params list by name.
                // We compare by name only, not the full TypeParam struct, because
                // the typeclass constraint might differ between generic_type and params.
                //
                // The bound variable index is computed as (n - 1 - i) because after the
                // caller wraps the result with Pi binders for type params, the first type
                // param (index 0) will be at the outermost binder, accessible via BV(n-1)
                // from inside, while the last type param (index n-1) will be at the
                // innermost binder, accessible via BV(0).
                let n = params.len();
                for (i, param) in params.iter().enumerate() {
                    if let AcornType::Variable(p) = param {
                        if p.name == type_param.name {
                            return Term::atom(Atom::BoundVariable((n - 1 - i) as u16));
                        }
                    }
                }
                panic!(
                    "Type variable {:?} not found in params: {:?}",
                    type_param, params
                );
            }

            AcornType::Arbitrary(type_param) => {
                // Arbitrary types should be registered, use as ground types
                let ground_id = self
                    .arbitrary_to_ground_id
                    .get(type_param)
                    .unwrap_or_else(|| panic!("Arbitrary type {:?} not registered", type_param));
                Term::ground_type(*ground_id)
            }
        }
    }

    /// Convert a type Term back to an AcornType.
    /// This is the inverse of `to_type_term`.
    pub fn type_term_to_acorn_type(&self, type_term: &Term) -> AcornType {
        // Check for built-in types first
        if type_term.as_ref().is_bool_type() {
            return AcornType::Bool;
        }
        if type_term.as_ref().is_empty_type() {
            return AcornType::Empty;
        }
        // TypeSort is the "type of types" - it's a kind, not a type.
        // It should not be converted to an AcornType.
        if type_term.as_ref().is_type_sort() {
            panic!(
                "type_term_to_acorn_type: TypeSort cannot be converted to AcornType. \
                 TypeSort is the type of types, not a value type."
            );
        }

        // Check for user-defined ground type
        if let Some(ground_id) = type_term.as_ref().as_type_atom() {
            // Ground type - look up in ground_id_to_type
            return self.ground_id_to_type[ground_id.as_u16() as usize].clone();
        }

        // Check for Pi type
        if let Some((input, output)) = type_term.as_ref().split_pi() {
            // Pi type: convert to function type
            // Pi(A, Pi(B, C)) becomes (A, B) -> C
            // But Pi(Type, ...) is a dependent type for polymorphic functions - skip the Type argument
            let input_owned = input.to_owned();
            let mut arg_types = if input_owned.as_ref().is_type_sort() {
                vec![] // Skip Type arguments (they're type parameters, not value arguments)
            } else {
                vec![self.type_term_to_acorn_type(&input_owned)]
            };

            // Uncurry nested Pi types
            let mut current_output = output.to_owned();
            while let Some((next_input, next_output)) = current_output.as_ref().split_pi() {
                let next_input_owned = next_input.to_owned();
                // Skip Type arguments in nested Pi types too
                if !next_input_owned.as_ref().is_type_sort() {
                    arg_types.push(self.type_term_to_acorn_type(&next_input_owned));
                }
                current_output = next_output.to_owned();
            }

            let return_type = self.type_term_to_acorn_type(&current_output);

            let ft = FunctionType {
                arg_types,
                return_type: Box::new(return_type),
            };
            return AcornType::Function(ft);
        }

        // Check for type application
        if let Some((head, args)) = type_term.as_ref().split_application_multi() {
            // Type application like List[Int]
            // Extract the datatype from head (must be a ground type)
            let base_type = self.type_term_to_acorn_type(&head);
            let datatype = match &base_type {
                AcornType::Data(dt, params) if params.is_empty() => dt.clone(),
                _ => panic!(
                    "Expected ground data type in type application, got {:?}",
                    base_type
                ),
            };

            // Convert parameter types
            let params: Vec<AcornType> = args
                .iter()
                .map(|arg| self.type_term_to_acorn_type(arg))
                .collect();

            return AcornType::Data(datatype, params);
        }

        // Handle BoundVariable - these can appear in dependent types that weren't fully instantiated
        // Convert to type variable for display purposes
        if type_term.as_ref().is_atomic() {
            if let Atom::BoundVariable(i) = type_term.as_ref().get_head_atom() {
                // Create a synthetic type variable for display purposes
                let type_param = TypeParam {
                    name: format!("T{}", i),
                    typeclass: None,
                };
                return AcornType::Variable(type_param);
            }
        }

        // Handle FreeVariable - these are used for type variables in polymorphic mode
        if type_term.as_ref().is_atomic() {
            if let Atom::FreeVariable(i) = type_term.as_ref().get_head_atom() {
                // Create a synthetic type variable for display purposes
                // Use "x" prefix to match the free variable naming convention
                let type_param = TypeParam {
                    name: format!("x{}", i),
                    typeclass: None,
                };
                return AcornType::Variable(type_param);
            }
        }

        // Handle Typeclass - these are used as type constraints in polymorphic mode
        if type_term.as_ref().is_atomic() {
            if let Atom::Typeclass(tc_id) = type_term.as_ref().get_head_atom() {
                // Convert back to a Typeclass. We need to look up the name.
                if let Some(typeclass) = self.id_to_typeclass.get(tc_id.as_u16() as usize) {
                    // Return as a type variable constrained to this typeclass
                    let type_param = TypeParam {
                        name: "S".to_string(), // Generic name for the constrained type
                        typeclass: Some(typeclass.clone()),
                    };
                    return AcornType::Variable(type_param);
                }
            }
        }

        panic!("Unexpected type Term structure: {:?}", type_term);
    }

    /// Get the id for a typeclass if it exists, otherwise return an error.
    pub fn get_typeclass_id(&self, typeclass: &Typeclass) -> Result<TypeclassId, String> {
        self.typeclass_to_id
            .get(typeclass)
            .copied()
            .ok_or_else(|| format!("Typeclass {} not registered in type store", typeclass.name))
    }

    /// Returns the id for the typeclass, adding it if it doesn't already exist.
    pub fn add_typeclass(&mut self, typeclass: &Typeclass) -> TypeclassId {
        if let Some(id) = self.typeclass_to_id.get(typeclass) {
            return *id;
        }

        self.id_to_typeclass.push(typeclass.clone());
        self.typeclass_extends.push(HashSet::new());
        self.typeclass_instances.push(HashSet::new());
        let id = TypeclassId::new((self.id_to_typeclass.len() - 1) as u16);
        self.typeclass_to_id.insert(typeclass.clone(), id);
        id
    }

    /// Get the typeclass for a given id.
    pub fn get_typeclass(&self, typeclass_id: TypeclassId) -> &Typeclass {
        &self.id_to_typeclass[typeclass_id.as_u16() as usize]
    }

    /// Get the TypeclassId for a typeclass by name.
    /// Returns None if not found.
    #[cfg(test)]
    pub fn get_typeclass_id_by_name(&self, name: &str) -> Option<TypeclassId> {
        for (i, tc) in self.id_to_typeclass.iter().enumerate() {
            if tc.name == name {
                return Some(TypeclassId::new(i as u16));
            }
        }
        None
    }

    /// Register that one typeclass extends another.
    /// This should be the direct extension relationship; the transitive closure is computed automatically.
    pub fn add_typeclass_extends(&mut self, typeclass_id: TypeclassId, base_id: TypeclassId) {
        // Add the direct extension
        self.typeclass_extends[typeclass_id.as_u16() as usize].insert(base_id);

        // Also add all typeclasses that the base extends (transitive closure)
        let base_extends: Vec<TypeclassId> = self.typeclass_extends[base_id.as_u16() as usize]
            .iter()
            .copied()
            .collect();
        for transitive_base in base_extends {
            self.typeclass_extends[typeclass_id.as_u16() as usize].insert(transitive_base);
        }
    }

    /// Register that a ground type is an instance of a typeclass.
    fn add_instance(&mut self, ground_id: GroundTypeId, typeclass_id: TypeclassId) {
        self.typeclass_instances[typeclass_id.as_u16() as usize].insert(ground_id);
    }

    /// Register that a type (given as AcornType) is an instance of a typeclass.
    /// The type must be a ground type (bare data type with no params).
    pub fn add_type_instance(&mut self, acorn_type: &AcornType, typeclass_id: TypeclassId) {
        // Ensure the type is registered
        self.add_type_internal(acorn_type);

        // Get the GroundTypeId - only ground types can be typeclass instances
        let ground_id = match acorn_type {
            AcornType::Data(datatype, params) if params.is_empty() => self
                .datatype_to_ground_id
                .get(datatype)
                .copied()
                .expect("Data type should have been registered"),
            _ => panic!(
                "Only bare data types can be typeclass instances, got {:?}",
                acorn_type
            ),
        };
        self.add_instance(ground_id, typeclass_id);
    }

    /// Check if one typeclass extends another (directly or transitively).
    pub fn typeclass_extends(&self, typeclass_id: TypeclassId, base_id: TypeclassId) -> bool {
        self.typeclass_extends
            .get(typeclass_id.as_u16() as usize)
            .map_or(false, |extends| extends.contains(&base_id))
    }

    /// Get all typeclasses that a given typeclass extends (directly or transitively).
    pub fn get_typeclass_extends(
        &self,
        typeclass_id: TypeclassId,
    ) -> impl Iterator<Item = TypeclassId> + '_ {
        self.typeclass_extends
            .get(typeclass_id.as_u16() as usize)
            .into_iter()
            .flat_map(|extends| extends.iter().copied())
    }

    /// Creates a Term representing a typeclass.
    /// This is used when a type variable is constrained to a typeclass.
    pub fn typeclass_to_term(&self, typeclass_id: TypeclassId) -> Term {
        Term::atom(Atom::Typeclass(typeclass_id))
    }

    /// Checks if a ground type is an instance of a typeclass.
    pub fn is_instance_of(&self, ground_id: GroundTypeId, typeclass_id: TypeclassId) -> bool {
        self.typeclass_instances
            .get(typeclass_id.as_u16() as usize)
            .map_or(false, |instances| instances.contains(&ground_id))
    }

    /// Get the typeclass constraint for a ground type, if it represents an arbitrary type
    /// with a typeclass constraint.
    /// Returns the TypeclassId if the ground type is an arbitrary type with a typeclass.
    pub fn get_arbitrary_typeclass(&self, ground_id: GroundTypeId) -> Option<TypeclassId> {
        // Look through arbitrary_to_ground_id to find if this ground_id is an arbitrary type
        for (type_param, &gid) in &self.arbitrary_to_ground_id {
            if gid == ground_id {
                // Found it - check if it has a typeclass constraint
                if let Some(tc) = &type_param.typeclass {
                    return self.typeclass_to_id.get(tc).copied();
                }
            }
        }
        None
    }
}

impl Default for TypeStore {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_store_defaults() {
        let store = TypeStore::new();
        // Empty and Bool are now Symbol variants - verify via to_type_term
        let empty_term = store.to_type_term(&AcornType::Empty);
        assert!(empty_term.as_ref().is_empty_type());
        let bool_term = store.to_type_term(&AcornType::Bool);
        assert!(bool_term.as_ref().is_bool_type());
    }

    #[test]
    fn test_to_type_term_ground() {
        let store = TypeStore::new();

        // Built-in types should convert to their Symbol variants
        let bool_term = store.to_type_term(&AcornType::Bool);
        assert!(bool_term.as_ref().is_atomic());
        assert!(bool_term.as_ref().is_bool_type());

        let empty_term = store.to_type_term(&AcornType::Empty);
        assert!(empty_term.as_ref().is_atomic());
        assert!(empty_term.as_ref().is_empty_type());
    }

    #[test]
    fn test_to_type_term_function() {
        let mut store = TypeStore::new();

        // Create Bool -> Bool function type
        let bool_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        store.add_type(&bool_to_bool);

        let type_term = store.to_type_term(&bool_to_bool);
        assert!(type_term.as_ref().is_pi());

        let (input, output) = type_term.as_ref().split_pi().unwrap();
        assert!(input.is_bool_type());
        assert!(output.is_bool_type());
    }

    #[test]
    fn test_to_type_term_curried_function() {
        let mut store = TypeStore::new();

        // Create (Bool, Bool) -> Bool function type
        // Should become Pi(Bool, Pi(Bool, Bool))
        let bool2_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool, AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        store.add_type(&bool2_to_bool);

        let type_term = store.to_type_term(&bool2_to_bool);
        assert!(type_term.as_ref().is_pi());

        // First Pi: Bool -> (Bool -> Bool)
        let (input1, rest) = type_term.as_ref().split_pi().unwrap();
        assert!(input1.is_bool_type());
        assert!(rest.is_pi());

        // Second Pi: Bool -> Bool
        let (input2, output) = rest.split_pi().unwrap();
        assert!(input2.is_bool_type());
        assert!(output.is_bool_type());
    }

    #[test]
    fn test_to_type_term_parameterized_data() {
        use crate::elaborator::acorn_type::Datatype;
        use crate::module::ModuleId;

        let mut store = TypeStore::new();

        // Create a parameterized type like List[Bool]
        let list_datatype = Datatype {
            module_id: ModuleId(0),
            name: "List".to_string(),
        };
        let list_bool = AcornType::Data(list_datatype.clone(), vec![AcornType::Bool]);
        store.add_type(&list_bool);

        // The bare constructor should have been auto-registered
        let list_ground = store
            .get_datatype_id(&list_datatype)
            .expect("List should be registered");

        // Get the type term
        let type_term = store.to_type_term(&list_bool);

        // It should be an Application
        assert!(
            type_term.as_ref().is_application(),
            "Expected Application, got {:?}",
            type_term
        );

        // Check structure using split_application_multi
        let (head, args) = type_term.as_ref().split_application_multi().unwrap();

        // The head should be the bare List constructor's GroundTypeId
        assert_eq!(
            head.as_ref().as_type_atom(),
            Some(list_ground),
            "Head should be List constructor, got {:?}",
            head
        );

        // There should be exactly one argument (Bool)
        assert_eq!(args.len(), 1, "Expected 1 argument, got {}", args.len());
        assert!(
            args[0].as_ref().is_bool_type(),
            "Argument should be Bool, got {:?}",
            args[0]
        );
    }

    #[test]
    fn test_to_type_term_nested_parameterized_data() {
        use crate::elaborator::acorn_type::Datatype;
        use crate::module::ModuleId;

        let mut store = TypeStore::new();

        // Create List[List[Bool]] - nested parameterized type
        let list_datatype = Datatype {
            module_id: ModuleId(0),
            name: "List".to_string(),
        };
        let list_bool = AcornType::Data(list_datatype.clone(), vec![AcornType::Bool]);
        let list_list_bool = AcornType::Data(list_datatype.clone(), vec![list_bool.clone()]);
        store.add_type(&list_list_bool);

        // Get GroundTypeId for List constructor
        let list_ground = store
            .get_datatype_id(&list_datatype)
            .expect("List should be registered");

        // Get the type term for List[List[Bool]]
        let type_term = store.to_type_term(&list_list_bool);

        // It should be an Application
        assert!(
            type_term.as_ref().is_application(),
            "Expected Application, got {:?}",
            type_term
        );

        // Check structure using split_application_multi
        let (head, args) = type_term.as_ref().split_application_multi().unwrap();

        // The head should be the bare List constructor
        assert_eq!(
            head.as_ref().as_type_atom(),
            Some(list_ground),
            "Head should be List constructor, got {:?}",
            head
        );

        // There should be exactly one argument (List[Bool])
        assert_eq!(args.len(), 1, "Expected 1 argument, got {}", args.len());

        // The argument should be List[Bool], which is also an Application
        let inner_term = &args[0];
        assert!(
            inner_term.as_ref().is_application(),
            "Inner type should be Application"
        );

        let (inner_head, inner_args) = inner_term.as_ref().split_application_multi().unwrap();
        assert_eq!(
            inner_head.as_ref().as_type_atom(),
            Some(list_ground),
            "Inner head should also be List constructor"
        );
        assert_eq!(inner_args.len(), 1, "Inner should have 1 argument");
        assert!(
            inner_args[0].as_ref().is_bool_type(),
            "Innermost argument should be Bool"
        );
    }

    #[test]
    fn test_typeclass_to_term() {
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let mut store = TypeStore::new();

        // Register a typeclass
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = store.add_typeclass(&monoid);

        // Create a term for the typeclass
        let term = store.typeclass_to_term(monoid_id);

        // Verify it's an atomic term with Typeclass atom
        assert!(term.as_ref().is_atomic());
        assert_eq!(term.as_ref().as_typeclass(), Some(monoid_id));
    }

    #[test]
    fn test_is_instance_of() {
        use crate::elaborator::acorn_type::{Datatype, Typeclass};
        use crate::module::ModuleId;

        let mut store = TypeStore::new();

        // Register a typeclass
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = store.add_typeclass(&monoid);

        // Register data types
        let int_type = Datatype {
            module_id: ModuleId(0),
            name: "Int".to_string(),
        };
        let int_acorn = AcornType::Data(int_type.clone(), vec![]);
        store.add_type(&int_acorn);
        let int_id = store.get_datatype_id(&int_type).unwrap();

        let nat_type = Datatype {
            module_id: ModuleId(0),
            name: "Nat".to_string(),
        };
        let nat_acorn = AcornType::Data(nat_type.clone(), vec![]);
        store.add_type(&nat_acorn);
        let nat_id = store.get_datatype_id(&nat_type).unwrap();

        // Before adding as instance, should return false
        assert!(!store.is_instance_of(int_id, monoid_id));

        // Add Int as instance of Monoid
        store.add_type_instance(&int_acorn, monoid_id);

        // Now should return true
        assert!(store.is_instance_of(int_id, monoid_id));

        // Nat should not be an instance (we didn't add it)
        assert!(!store.is_instance_of(nat_id, monoid_id));
    }
}
