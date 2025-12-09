use std::collections::{HashMap, HashSet};

use crate::elaborator::acorn_type::{AcornType, FunctionType, Typeclass};
use crate::kernel::atom::Atom;
use crate::kernel::closed_type::ClosedType;
use crate::kernel::term::TermComponent;
use crate::kernel::types::{GroundTypeId, TypeId, TypeclassId};

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
            AcornType::Data(datatype, params) => {
                // For parameterized types, first ensure the bare constructor exists
                // so it gets its own TypeId/GroundTypeId for use in ClosedType
                if !params.is_empty() {
                    let bare_constructor = AcornType::Data(datatype.clone(), vec![]);
                    self.add_type(&bare_constructor);
                }
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

    /// Get the GroundTypeId for a TypeId if it refers to a ground type.
    /// Returns None if the type is a function type or parameterized type.
    /// Ground types are those with no internal structure: Empty, Bool, and data types without parameters.
    pub fn get_ground_type_id(&self, type_id: TypeId) -> Option<GroundTypeId> {
        // A type is ground if it has no function info (not a function type)
        // and is not a parameterized data type
        if self.get_function_info(type_id).is_some() {
            return None;
        }

        // Check if it's a parameterized data type
        let acorn_type = self.get_type(type_id);
        match acorn_type {
            AcornType::Data(_, params) if !params.is_empty() => None,
            _ => Some(GroundTypeId::new(type_id.as_u16())),
        }
    }

    /// Convert a TypeId to a ClosedType.
    /// This converts the AcornType representation to the flattened ClosedType format.
    pub fn type_id_to_closed_type(&self, type_id: TypeId) -> ClosedType {
        let acorn_type = self.get_type(type_id);
        self.acorn_type_to_closed_type(acorn_type, type_id)
    }

    /// Convert an AcornType to a ClosedType, given the TypeId for this type.
    /// The type_id is passed so ground types can embed it directly.
    fn acorn_type_to_closed_type(&self, acorn_type: &AcornType, type_id: TypeId) -> ClosedType {
        match acorn_type {
            // Ground types: Empty, Bool, and Data types with no params
            AcornType::Empty | AcornType::Bool => {
                let ground_id = self
                    .get_ground_type_id(type_id)
                    .expect("Empty/Bool should be ground types");
                ClosedType::ground(ground_id)
            }

            AcornType::Data(_, params) if params.is_empty() => {
                // Data type with no parameters is a ground type
                let ground_id = self
                    .get_ground_type_id(type_id)
                    .expect("Data type with no params should be ground");
                ClosedType::ground(ground_id)
            }

            AcornType::Data(datatype, params) => {
                // Data type with parameters: build Application
                // e.g., List[Int] -> [Application{span}, Atom(List), Atom(Int)]
                let mut components = Vec::new();

                // Head is the bare constructor (e.g., List without params)
                // which was auto-registered in add_type()
                let bare_constructor = AcornType::Data(datatype.clone(), vec![]);
                let constructor_type_id = self
                    .get_type_id(&bare_constructor)
                    .expect("Bare constructor should have been added");
                let constructor_ground_id = self
                    .get_ground_type_id(constructor_type_id)
                    .expect("Bare constructor should be a ground type");
                components.push(TermComponent::Atom(Atom::Type(constructor_ground_id)));

                // Add each parameter
                for param in params {
                    let param_id = self.get_type_id(param).expect("Parameter type not found");
                    let param_closed = self.type_id_to_closed_type(param_id);
                    // If param is compound, wrap in Application
                    if param_closed.components().len() == 1 {
                        components.extend(param_closed.components().iter().copied());
                    } else {
                        components.push(TermComponent::Application {
                            span: param_closed.components().len() as u16 + 1,
                        });
                        components.extend(param_closed.components().iter().copied());
                    }
                }

                // Update span for the outer Application
                let total_span = components.len() as u16 + 1;
                let mut result = vec![TermComponent::Application { span: total_span }];
                result.extend(components);
                ClosedType::from_components(result)
            }

            AcornType::Function(ft) => {
                // Function type: build nested Pi types (curried)
                // (A, B) -> C becomes Pi(A, Pi(B, C))
                self.function_type_to_closed_type(ft)
            }

            AcornType::Variable(_) | AcornType::Arbitrary(_) => {
                // Type variables/arbitrary types are not fully closed.
                // For now, represent them as a ground type using the TypeId.
                // This is a temporary representation until all types are fully closed.
                let ground_id = GroundTypeId::new(type_id.as_u16());
                ClosedType::ground(ground_id)
            }
        }
    }

    /// Convert a FunctionType to a ClosedType with nested Pi types.
    fn function_type_to_closed_type(&self, ft: &FunctionType) -> ClosedType {
        // Get return type as ClosedType
        let return_id = self
            .get_type_id(&ft.return_type)
            .expect("Return type not found");
        let mut result = self.type_id_to_closed_type(return_id);

        // Build Pi types from right to left: (A, B, C) -> R becomes Pi(A, Pi(B, Pi(C, R)))
        for arg_type in ft.arg_types.iter().rev() {
            let arg_id = self.get_type_id(arg_type).expect("Arg type not found");
            let arg_closed = self.type_id_to_closed_type(arg_id);
            result = ClosedType::pi(arg_closed, result);
        }

        result
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

    #[test]
    fn test_get_ground_type_id() {
        let mut store = TypeStore::new();

        // EMPTY and BOOL should be ground types
        assert!(store.get_ground_type_id(EMPTY).is_some());
        assert!(store.get_ground_type_id(BOOL).is_some());

        // Function type should not be ground
        let bool_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let func_id = store.add_type(&bool_to_bool);
        assert!(store.get_ground_type_id(func_id).is_none());
    }

    #[test]
    fn test_type_id_to_closed_type_ground() {
        let store = TypeStore::new();

        // Ground types should convert to simple ClosedType::ground()
        let bool_closed = store.type_id_to_closed_type(BOOL);
        assert!(bool_closed.is_ground());
        let bool_ground = store.get_ground_type_id(BOOL).unwrap();
        assert_eq!(bool_closed.as_ground(), Some(bool_ground));

        let empty_closed = store.type_id_to_closed_type(EMPTY);
        assert!(empty_closed.is_ground());
        let empty_ground = store.get_ground_type_id(EMPTY).unwrap();
        assert_eq!(empty_closed.as_ground(), Some(empty_ground));
    }

    #[test]
    fn test_type_id_to_closed_type_function() {
        let mut store = TypeStore::new();

        // Create Bool -> Bool function type
        let bool_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let type_id = store.add_type(&bool_to_bool);

        let closed = store.type_id_to_closed_type(type_id);
        assert!(closed.is_pi());

        let bool_ground = store.get_ground_type_id(BOOL).unwrap();
        let (input, output) = closed.as_pi().unwrap();
        assert_eq!(input.as_ground(), Some(bool_ground));
        assert_eq!(output.as_ground(), Some(bool_ground));
    }

    #[test]
    fn test_type_id_to_closed_type_curried_function() {
        let mut store = TypeStore::new();

        // Create (Bool, Bool) -> Bool function type
        // Should become Pi(Bool, Pi(Bool, Bool))
        let bool2_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool, AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let type_id = store.add_type(&bool2_to_bool);

        let closed = store.type_id_to_closed_type(type_id);
        assert!(closed.is_pi());

        let bool_ground = store.get_ground_type_id(BOOL).unwrap();

        // First Pi: Bool -> (Bool -> Bool)
        let (input1, rest) = closed.as_pi().unwrap();
        assert_eq!(input1.as_ground(), Some(bool_ground));
        assert!(rest.is_pi());

        // Second Pi: Bool -> Bool
        let (input2, output) = rest.as_pi().unwrap();
        assert_eq!(input2.as_ground(), Some(bool_ground));
        assert_eq!(output.as_ground(), Some(bool_ground));
    }

    #[test]
    fn test_type_id_to_closed_type_parameterized_data() {
        use crate::elaborator::acorn_type::Datatype;
        use crate::module::ModuleId;

        let mut store = TypeStore::new();

        // Create a parameterized type like List[Bool]
        let list_datatype = Datatype {
            module_id: ModuleId(0),
            name: "List".to_string(),
        };
        let list_bool = AcornType::Data(list_datatype.clone(), vec![AcornType::Bool]);
        let list_bool_id = store.add_type(&list_bool);

        // The bare constructor should have been auto-registered
        let bare_list = AcornType::Data(list_datatype, vec![]);
        let list_id = store.get_type_id(&bare_list).expect("List should exist");
        let list_ground = store
            .get_ground_type_id(list_id)
            .expect("List should be ground");

        // Get the ClosedType
        let closed = store.type_id_to_closed_type(list_bool_id);

        // It should be an Application
        assert!(
            matches!(
                closed.components().first(),
                Some(TermComponent::Application { .. })
            ),
            "Expected Application, got {:?}",
            closed
        );

        // The head (second component) should be the bare List constructor's GroundTypeId
        assert!(
            matches!(
                closed.components().get(1),
                Some(TermComponent::Atom(Atom::Type(t))) if *t == list_ground
            ),
            "Head should be List constructor, got {:?}",
            closed.components().get(1)
        );

        // The argument should be Bool
        let bool_ground = store.get_ground_type_id(BOOL).unwrap();
        assert!(
            matches!(
                closed.components().get(2),
                Some(TermComponent::Atom(Atom::Type(t))) if *t == bool_ground
            ),
            "Argument should be Bool, got {:?}",
            closed.components().get(2)
        );
    }
}
