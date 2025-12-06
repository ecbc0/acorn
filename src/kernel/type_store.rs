use std::collections::{HashMap, HashSet};

use crate::elaborator::acorn_type::{AcornType, FunctionType, Typeclass};
use crate::kernel::types::{TypeId, TypeclassId};

/// Manages the bidirectional mapping between AcornTypes and TypeIds,
/// as well as typeclasses and their relationships to types.
#[derive(Clone)]
pub struct TypeStore {
    /// type_to_type_id[acorn_type] is the TypeId
    type_to_type_id: HashMap<AcornType, TypeId>,

    /// type_id_to_type[type_id] is the AcornType
    type_id_to_type: Vec<AcornType>,

    /// For function types, stores (domain, codomain) as TypeIds.
    /// For non-function types, stores None.
    /// Indexed by TypeId.
    function_info: Vec<Option<(TypeId, TypeId)>>,

    /// typeclass_to_id[typeclass] is the TypeclassId
    typeclass_to_id: HashMap<Typeclass, TypeclassId>,

    /// id_to_typeclass[typeclass_id] is the Typeclass
    id_to_typeclass: Vec<Typeclass>,

    /// typeclass_extends[typeclass_id] is the set of TypeclassIds that this typeclass extends.
    /// This is the transitive closure, so if A extends B and B extends C, then A's set contains both B and C.
    typeclass_extends: Vec<HashSet<TypeclassId>>,

    /// typeclass_instances[typeclass_id] is the set of TypeIds that are instances of this typeclass.
    typeclass_instances: Vec<HashSet<TypeId>>,
}

impl TypeStore {
    pub fn new() -> TypeStore {
        let mut store = TypeStore {
            type_to_type_id: HashMap::new(),
            type_id_to_type: vec![],
            function_info: vec![],
            typeclass_to_id: HashMap::new(),
            id_to_typeclass: vec![],
            typeclass_extends: vec![],
            typeclass_instances: vec![],
        };
        store.add_type(&AcornType::Empty);
        store.add_type(&AcornType::Bool);
        store
    }

    /// Get the id for a type if it exists, otherwise return an error.
    pub fn get_type_id(&self, acorn_type: &AcornType) -> Result<TypeId, String> {
        self.type_to_type_id
            .get(acorn_type)
            .copied()
            .ok_or_else(|| format!("Type {} not registered in type store", acorn_type))
    }

    /// Returns the id for the new type.
    pub fn add_type(&mut self, acorn_type: &AcornType) -> TypeId {
        if let Some(type_id) = self.type_to_type_id.get(acorn_type) {
            return *type_id;
        }

        // First, recursively add all component types and compute function_info
        let func_info = match acorn_type {
            AcornType::Function(ft) => {
                // Add all argument types
                for arg_type in &ft.arg_types {
                    self.add_type(arg_type);
                }
                // Add the return type
                self.add_type(&ft.return_type);

                // Compute curried function info: (A, B, C) -> R becomes A -> (B -> (C -> R))
                // So domain is first arg, codomain is the rest curried
                if ft.arg_types.is_empty() {
                    // Degenerate case - no args means it's just the return type
                    None
                } else {
                    let domain_id = self.get_type_id(&ft.arg_types[0]).unwrap();
                    let codomain_id = if ft.arg_types.len() == 1 {
                        // Single arg: codomain is just the return type
                        self.get_type_id(&ft.return_type).unwrap()
                    } else {
                        // Multiple args: codomain is the curried remainder
                        let rest_ft = AcornType::Function(FunctionType {
                            arg_types: ft.arg_types[1..].to_vec(),
                            return_type: ft.return_type.clone(),
                        });
                        self.add_type(&rest_ft)
                    };
                    Some((domain_id, codomain_id))
                }
            }
            AcornType::Data(_, params) => {
                // Add all type parameters
                for param in params {
                    self.add_type(param);
                }
                None
            }
            _ => None,
        };

        // Now add the type itself
        self.type_id_to_type.push(acorn_type.clone());
        self.function_info.push(func_info);
        let id = TypeId::new((self.type_id_to_type.len() - 1) as u16);
        self.type_to_type_id.insert(acorn_type.clone(), id);
        id
    }

    pub fn get_type(&self, type_id: TypeId) -> &AcornType {
        &self.type_id_to_type[type_id.as_u16() as usize]
    }

    /// For function types, returns (domain, codomain) as TypeIds.
    /// For non-function types, returns None.
    /// Function types are treated as curried, so (A, B) -> C has domain A and codomain (B -> C).
    pub fn get_function_info(&self, type_id: TypeId) -> Option<(TypeId, TypeId)> {
        self.function_info
            .get(type_id.as_u16() as usize)
            .copied()
            .flatten()
    }

    /// Apply a function type to get its codomain.
    /// Returns None if the type is not a function type.
    pub fn apply_type(&self, type_id: TypeId) -> Option<TypeId> {
        self.get_function_info(type_id)
            .map(|(_, codomain)| codomain)
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

    /// Register that a type is an instance of a typeclass.
    pub fn add_instance(&mut self, type_id: TypeId, typeclass_id: TypeclassId) {
        self.typeclass_instances[typeclass_id.as_u16() as usize].insert(type_id);
    }

    /// Check if a type is an instance of a typeclass.
    pub fn is_instance_of(&self, type_id: TypeId, typeclass_id: TypeclassId) -> bool {
        self.typeclass_instances
            .get(typeclass_id.as_u16() as usize)
            .map_or(false, |instances| instances.contains(&type_id))
    }

    /// Check if one typeclass extends another (directly or transitively).
    pub fn typeclass_extends(&self, typeclass_id: TypeclassId, base_id: TypeclassId) -> bool {
        self.typeclass_extends
            .get(typeclass_id.as_u16() as usize)
            .map_or(false, |extends| extends.contains(&base_id))
    }
}

impl Default for TypeStore {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::types::{BOOL, EMPTY};

    use super::*;

    #[test]
    fn test_type_store_defaults() {
        let store = TypeStore::new();
        assert_eq!(store.get_type(EMPTY), &AcornType::Empty);
        assert_eq!(store.get_type(BOOL), &AcornType::Bool);
    }
}
