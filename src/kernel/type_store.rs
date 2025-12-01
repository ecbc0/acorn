use std::collections::HashMap;

use crate::acorn_type::AcornType;
use crate::kernel::term::TypeId;

/// Manages the bidirectional mapping between AcornTypes and TypeIds.
#[derive(Clone)]
pub struct TypeStore {
    /// type_to_type_id[acorn_type] is the TypeId
    type_to_type_id: HashMap<AcornType, TypeId>,

    /// type_id_to_type[type_id] is the AcornType
    type_id_to_type: Vec<AcornType>,
}

impl TypeStore {
    pub fn new() -> TypeStore {
        let mut store = TypeStore {
            type_to_type_id: HashMap::new(),
            type_id_to_type: vec![],
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
            .ok_or_else(|| format!("Type {} not registered in normalization map", acorn_type))
    }

    /// Returns the id for the new type.
    pub fn add_type(&mut self, acorn_type: &AcornType) -> TypeId {
        if let Some(type_id) = self.type_to_type_id.get(acorn_type) {
            return *type_id;
        }

        // First, recursively add all component types
        match acorn_type {
            AcornType::Function(ft) => {
                // Add all argument types
                for arg_type in &ft.arg_types {
                    self.add_type(arg_type);
                }
                // Add the return type
                self.add_type(&ft.return_type);
            }
            AcornType::Data(_, params) => {
                // Add all type parameters
                for param in params {
                    self.add_type(param);
                }
            }
            _ => {}
        }

        // Now add the type itself
        self.type_id_to_type.push(acorn_type.clone());
        let id = TypeId::new((self.type_id_to_type.len() - 1) as u16);
        self.type_to_type_id.insert(acorn_type.clone(), id);
        id
    }

    pub fn get_type(&self, type_id: TypeId) -> &AcornType {
        &self.type_id_to_type[type_id.as_u16() as usize]
    }
}

impl Default for TypeStore {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::term::{BOOL, EMPTY};

    use super::*;

    #[test]
    fn test_type_store_defaults() {
        let store = TypeStore::new();
        assert_eq!(store.get_type(EMPTY), &AcornType::Empty);
        assert_eq!(store.get_type(BOOL), &AcornType::Bool);
    }
}
