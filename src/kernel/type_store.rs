use std::collections::HashMap;

use crate::elaborator::acorn_type::{AcornType, FunctionType};
use crate::kernel::types::TypeId;

/// Manages the bidirectional mapping between AcornTypes and TypeIds.
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
}

impl TypeStore {
    pub fn new() -> TypeStore {
        let mut store = TypeStore {
            type_to_type_id: HashMap::new(),
            type_id_to_type: vec![],
            function_info: vec![],
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
