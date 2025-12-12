use std::collections::{HashMap, HashSet};

use crate::elaborator::acorn_type::{AcornType, Datatype, FunctionType, TypeParam, Typeclass};
use crate::kernel::closed_type::ClosedType;
use crate::kernel::types::{GroundTypeId, TypeclassId, BOOL, EMPTY};

/// Manages ground type registration and typeclass relationships.
#[derive(Clone)]
pub struct TypeStore {
    /// ground_id_to_type[ground_id] is the AcornType for that ground type.
    /// Only ground types are stored here.
    ground_id_to_type: Vec<AcornType>,

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
        let mut store = TypeStore {
            ground_id_to_type: vec![],
            datatype_to_ground_id: HashMap::new(),
            arbitrary_to_ground_id: HashMap::new(),
            typeclass_to_id: HashMap::new(),
            id_to_typeclass: vec![],
            typeclass_extends: vec![],
            typeclass_instances: vec![],
        };
        store.add_type_internal(&AcornType::Empty);
        store.add_type_internal(&AcornType::Bool);
        store
    }

    /// Register a type in the type store. Call this before using to_closed_type()
    /// to ensure ground types are registered.
    pub fn add_type(&mut self, acorn_type: &AcornType) {
        self.add_type_internal(acorn_type);
    }

    /// Internal implementation that registers ground types.
    /// Only ground types (Empty, Bool, bare Data types, Arbitrary) get GroundTypeIds.
    /// Non-ground types (Function, parameterized Data) are just recursively processed.
    fn add_type_internal(&mut self, acorn_type: &AcornType) {
        match acorn_type {
            // Empty and Bool: register if not already (they get EMPTY and BOOL)
            AcornType::Empty | AcornType::Bool => {
                // These are registered once in new() - the ground_id_to_type index matches the constants
                if self.ground_id_to_type.is_empty()
                    || (self.ground_id_to_type.len() == 1 && *acorn_type == AcornType::Bool)
                {
                    self.ground_id_to_type.push(acorn_type.clone());
                }
            }

            // Bare data type: assign a new GroundTypeId
            AcornType::Data(datatype, params) if params.is_empty() => {
                if self.datatype_to_ground_id.contains_key(datatype) {
                    return; // Already registered
                }
                let ground_id = self.next_ground_id();
                self.ground_id_to_type.push(acorn_type.clone());
                self.datatype_to_ground_id
                    .insert(datatype.clone(), ground_id);
            }

            // Parameterized data type: ensure bare constructor exists, then process params
            AcornType::Data(datatype, params) => {
                let bare_constructor = AcornType::Data(datatype.clone(), vec![]);
                self.add_type_internal(&bare_constructor);
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
                self.arbitrary_to_ground_id
                    .insert(type_param.clone(), ground_id);
            }

            // Variable types should not be registered
            AcornType::Variable(_) => {
                panic!("Variable types should not be registered: {:?}", acorn_type);
            }
        }
    }

    /// Allocate the next GroundTypeId.
    fn next_ground_id(&self) -> GroundTypeId {
        GroundTypeId::new(self.ground_id_to_type.len() as u16)
    }

    /// Get the GroundTypeId for a bare Datatype (no type parameters).
    /// Returns None if the datatype hasn't been registered.
    pub fn get_datatype_ground_id(&self, datatype: &Datatype) -> Option<GroundTypeId> {
        self.datatype_to_ground_id.get(datatype).copied()
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

    /// Get the ClosedType for an AcornType.
    /// Ground types must be registered first via add_type().
    pub fn get_closed_type(&self, acorn_type: &AcornType) -> Result<ClosedType, String> {
        Ok(self.to_closed_type(acorn_type))
    }

    /// Convert an AcornType to a ClosedType.
    /// Only ground types (Bool, Empty, bare data types, type variables) need to be registered.
    /// Function types and parameterized data types are constructed on the fly.
    pub fn to_closed_type(&self, acorn_type: &AcornType) -> ClosedType {
        match acorn_type {
            // Ground types: use constants
            AcornType::Empty => ClosedType::ground(EMPTY),
            AcornType::Bool => ClosedType::ground(BOOL),

            AcornType::Data(datatype, params) if params.is_empty() => {
                // Bare data type - use direct Datatype -> GroundTypeId lookup
                let ground_id = self
                    .datatype_to_ground_id
                    .get(datatype)
                    .unwrap_or_else(|| panic!("Data type {} not registered", datatype.name));
                ClosedType::ground(*ground_id)
            }

            AcornType::Data(datatype, params) => {
                // Parameterized data type: build Application using ClosedType::application()
                let constructor_ground = self
                    .datatype_to_ground_id
                    .get(datatype)
                    .unwrap_or_else(|| panic!("Data type {} not registered", datatype.name));
                let head = ClosedType::ground(*constructor_ground);

                let args: Vec<ClosedType> = params
                    .iter()
                    .map(|param| self.to_closed_type(param))
                    .collect();

                ClosedType::application(head, args)
            }

            AcornType::Function(ft) => {
                // Function type: build nested Pi types (curried)
                let mut result = self.to_closed_type(&ft.return_type);

                // Build Pi types from right to left
                for arg_type in ft.arg_types.iter().rev() {
                    let arg_closed = self.to_closed_type(arg_type);
                    result = ClosedType::pi(arg_closed, result);
                }

                result
            }

            AcornType::Variable(_) => {
                panic!(
                    "Variable types should not be converted to ClosedType: {:?}",
                    acorn_type
                );
            }

            AcornType::Arbitrary(type_param) => {
                // Arbitrary types must be registered
                let ground_id = self
                    .arbitrary_to_ground_id
                    .get(type_param)
                    .unwrap_or_else(|| panic!("Arbitrary type {:?} not registered", type_param));
                ClosedType::ground(*ground_id)
            }
        }
    }

    /// Convert a ClosedType back to an AcornType.
    /// This is the inverse of `to_closed_type`.
    pub fn closed_type_to_acorn_type(&self, closed_type: &ClosedType) -> AcornType {
        if let Some(ground_id) = closed_type.as_ground() {
            // Ground type - look up in ground_id_to_type
            return self.ground_id_to_type[ground_id.as_u16() as usize].clone();
        }

        if let Some((input, output)) = closed_type.as_pi() {
            // Pi type: convert to function type
            // Pi(A, Pi(B, C)) becomes (A, B) -> C
            let mut arg_types = vec![self.closed_type_to_acorn_type(&input)];

            // Uncurry nested Pi types
            let mut current_output = output;
            while let Some((next_input, next_output)) = current_output.as_pi() {
                arg_types.push(self.closed_type_to_acorn_type(&next_input));
                current_output = next_output;
            }

            let return_type = self.closed_type_to_acorn_type(&current_output);

            let ft = FunctionType {
                arg_types,
                return_type: Box::new(return_type),
            };
            return AcornType::Function(ft);
        }

        if let Some((head, args)) = closed_type.as_application() {
            // Type application like List[Int]
            // Extract the datatype from head (must be a ground type)
            let base_type = self.closed_type_to_acorn_type(&head);
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
                .map(|arg| self.closed_type_to_acorn_type(arg))
                .collect();

            return AcornType::Data(datatype, params);
        }

        panic!("Unexpected ClosedType structure: {:?}", closed_type);
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
        // EMPTY and BOOL are pre-registered - verify via to_closed_type
        let empty_closed = store.to_closed_type(&AcornType::Empty);
        assert_eq!(empty_closed.as_ground(), Some(EMPTY));
        let bool_closed = store.to_closed_type(&AcornType::Bool);
        assert_eq!(bool_closed.as_ground(), Some(BOOL));
    }

    #[test]
    fn test_to_closed_type_ground() {
        let store = TypeStore::new();

        // Ground types should convert to simple ClosedType::ground()
        let bool_closed = store.to_closed_type(&AcornType::Bool);
        assert!(bool_closed.is_ground());
        assert_eq!(bool_closed.as_ground(), Some(BOOL));

        let empty_closed = store.to_closed_type(&AcornType::Empty);
        assert!(empty_closed.is_ground());
        assert_eq!(empty_closed.as_ground(), Some(EMPTY));
    }

    #[test]
    fn test_to_closed_type_function() {
        let mut store = TypeStore::new();

        // Create Bool -> Bool function type
        let bool_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        store.add_type(&bool_to_bool);

        let closed = store.to_closed_type(&bool_to_bool);
        assert!(closed.is_pi());

        let (input, output) = closed.as_pi().unwrap();
        assert_eq!(input.as_ground(), Some(BOOL));
        assert_eq!(output.as_ground(), Some(BOOL));
    }

    #[test]
    fn test_to_closed_type_curried_function() {
        let mut store = TypeStore::new();

        // Create (Bool, Bool) -> Bool function type
        // Should become Pi(Bool, Pi(Bool, Bool))
        let bool2_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool, AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        store.add_type(&bool2_to_bool);

        let closed = store.to_closed_type(&bool2_to_bool);
        assert!(closed.is_pi());

        // First Pi: Bool -> (Bool -> Bool)
        let (input1, rest) = closed.as_pi().unwrap();
        assert_eq!(input1.as_ground(), Some(BOOL));
        assert!(rest.is_pi());

        // Second Pi: Bool -> Bool
        let (input2, output) = rest.as_pi().unwrap();
        assert_eq!(input2.as_ground(), Some(BOOL));
        assert_eq!(output.as_ground(), Some(BOOL));
    }

    #[test]
    fn test_to_closed_type_parameterized_data() {
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
            .get_datatype_ground_id(&list_datatype)
            .expect("List should be registered");

        // Get the ClosedType
        let closed = store.to_closed_type(&list_bool);

        // It should be an Application
        assert!(
            closed.is_application(),
            "Expected Application, got {:?}",
            closed
        );

        // Check structure using as_application
        let (head, args) = closed.as_application().unwrap();

        // The head should be the bare List constructor's GroundTypeId
        assert_eq!(
            head.as_ground(),
            Some(list_ground),
            "Head should be List constructor, got {:?}",
            head
        );

        // There should be exactly one argument (Bool)
        assert_eq!(args.len(), 1, "Expected 1 argument, got {}", args.len());
        assert_eq!(
            args[0].as_ground(),
            Some(BOOL),
            "Argument should be Bool, got {:?}",
            args[0]
        );
    }

    #[test]
    fn test_to_closed_type_nested_parameterized_data() {
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
            .get_datatype_ground_id(&list_datatype)
            .expect("List should be registered");

        // Get the ClosedType for List[List[Bool]]
        let closed = store.to_closed_type(&list_list_bool);

        // It should be an Application
        assert!(
            closed.is_application(),
            "Expected Application, got {:?}",
            closed
        );

        // Check structure using as_application
        let (head, args) = closed.as_application().unwrap();

        // The head should be the bare List constructor
        assert_eq!(
            head.as_ground(),
            Some(list_ground),
            "Head should be List constructor, got {:?}",
            head
        );

        // There should be exactly one argument (List[Bool])
        assert_eq!(args.len(), 1, "Expected 1 argument, got {}", args.len());

        // The argument should be List[Bool], which is also an Application
        let inner_closed = &args[0];
        assert!(
            inner_closed.is_application(),
            "Inner type should be Application"
        );

        let (inner_head, inner_args) = inner_closed.as_application().unwrap();
        assert_eq!(
            inner_head.as_ground(),
            Some(list_ground),
            "Inner head should also be List constructor"
        );
        assert_eq!(inner_args.len(), 1, "Inner should have 1 argument");
        assert_eq!(
            inner_args[0].as_ground(),
            Some(BOOL),
            "Innermost argument should be Bool"
        );
    }
}
