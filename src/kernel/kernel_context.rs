use crate::kernel::atom::Atom;
#[cfg(test)]
use crate::kernel::closed_type::ClosedType;
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::SymbolTable;
use crate::kernel::type_store::TypeStore;

/// KernelContext combines the TypeStore and SymbolTable that are needed
/// for working with kernel types and various kernel operations.
#[derive(Clone)]
pub struct KernelContext {
    pub type_store: TypeStore,
    pub symbol_table: SymbolTable,
}

impl KernelContext {
    pub fn new() -> KernelContext {
        KernelContext {
            type_store: TypeStore::new(),
            symbol_table: SymbolTable::new(),
        }
    }

    /// Returns a human-readable string representation of an atom.
    pub fn atom_str(&self, atom: &Atom) -> String {
        match atom {
            Atom::True => "true".to_string(),
            Atom::Symbol(Symbol::GlobalConstant(i)) => {
                self.symbol_table.name_for_global_id(*i).to_string()
            }
            Atom::Symbol(Symbol::ScopedConstant(i)) => {
                self.symbol_table.name_for_local_id(*i).to_string()
            }
            Atom::Symbol(Symbol::Monomorph(i)) => {
                format!("{}", self.symbol_table.get_monomorph(*i))
            }
            Atom::Variable(i) => format!("x{}", i),
            Atom::Symbol(Symbol::Synthetic(i)) => format!("s{}", i),
            Atom::Type(t) => format!("T{}", t.as_u16()),
        }
    }

    /// Creates a test KernelContext with pre-populated scoped constants (c0, c1, ..., c{n-1})
    /// all with EMPTY type. For use in tests that parse terms like "c0(x0)".
    #[cfg(test)]
    pub fn test_with_scoped_constants(n: usize) -> KernelContext {
        let mut ctx = KernelContext::new();
        for _ in 0..n {
            ctx.symbol_table.add_scoped_constant(ClosedType::empty());
        }
        ctx
    }

    /// Creates a test KernelContext with pre-populated scoped constants (c0, c1, ..., c{n-1})
    /// all with Bool type. For use in tests that need Bool-typed constants.
    #[cfg(test)]
    pub fn test_with_bool_scoped_constants(n: usize) -> KernelContext {
        let mut ctx = KernelContext::new();
        for _ in 0..n {
            ctx.symbol_table.add_scoped_constant(ClosedType::bool());
        }
        ctx
    }

    /// Creates a test KernelContext with pre-populated scoped constants with specified types.
    #[cfg(test)]
    pub fn test_with_scoped_constant_types(types: &[ClosedType]) -> KernelContext {
        let mut ctx = KernelContext::new();
        for closed_type in types {
            ctx.symbol_table.add_scoped_constant(closed_type.clone());
        }
        ctx
    }

    /// Creates a test KernelContext with pre-populated scoped constants, global constants,
    /// monomorphs, and synthetics. All types will be EMPTY.
    /// For use in tests that parse terms like "c0", "g0", "m0", "s0".
    #[cfg(test)]
    pub fn test_with_constants(num_scoped: usize, num_global: usize) -> KernelContext {
        let mut ctx = KernelContext::new();
        for _ in 0..num_scoped {
            ctx.symbol_table.add_scoped_constant(ClosedType::empty());
        }
        for _ in 0..num_global {
            ctx.symbol_table.add_global_constant(ClosedType::empty());
        }
        // Also add monomorphs for tests that use "m0", "m1", etc.
        for _ in 0..10 {
            ctx.symbol_table.add_monomorph(ClosedType::empty());
        }
        // Also add synthetics for tests that use "s0", "s1", etc.
        for _ in 0..10 {
            ctx.symbol_table.declare_synthetic(ClosedType::empty());
        }
        ctx
    }

    /// Creates a test KernelContext for tests that use arbitrary clause strings.
    /// All scoped/global constants are Bool type (c0-c9, g0-g9).
    /// All monomorphs are (Bool, Bool) -> Bool type (m0-m9).
    /// All synthetics are Bool type (s0-s9).
    /// This allows parsing clauses like "m0(c0, c1)" where functions take Bool args.
    #[cfg(test)]
    pub fn test_with_all_bool_types() -> KernelContext {
        use crate::elaborator::acorn_type::{AcornType, FunctionType};

        let mut ctx = KernelContext::new();

        // Create function types
        let bool_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let bool2_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool, AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        // Register the types first
        ctx.type_store.add_type(&bool_to_bool);
        ctx.type_store.add_type(&bool2_to_bool);
        let closed_bool_to_bool = ctx
            .type_store
            .get_closed_type(&bool_to_bool)
            .expect("type should be valid");
        let closed_bool2_to_bool = ctx
            .type_store
            .get_closed_type(&bool2_to_bool)
            .expect("type should be valid");

        // Scoped constants are Bool (c0-c9)
        for _ in 0..10 {
            ctx.symbol_table.add_scoped_constant(ClosedType::bool());
        }
        // Global constants are Bool -> Bool (g0-g9) for use as predicates
        for _ in 0..10 {
            ctx.symbol_table
                .add_global_constant(closed_bool_to_bool.clone());
        }

        // Monomorphs are (Bool, Bool) -> Bool functions (m0-m9)
        for _ in 0..10 {
            ctx.symbol_table.add_monomorph(closed_bool2_to_bool.clone());
        }

        // Synthetics are Bool (s0-s9)
        for _ in 0..10 {
            ctx.symbol_table.declare_synthetic(ClosedType::bool());
        }
        ctx
    }

    /// Creates a test KernelContext with pre-populated scoped and global constants with
    /// specified types.
    #[cfg(test)]
    pub fn test_with_constant_types(
        scoped_types: &[ClosedType],
        global_types: &[ClosedType],
    ) -> KernelContext {
        let mut ctx = KernelContext::new();
        for closed_type in scoped_types {
            ctx.symbol_table.add_scoped_constant(closed_type.clone());
        }
        for closed_type in global_types {
            ctx.symbol_table.add_global_constant(closed_type.clone());
        }
        ctx
    }

    /// Creates a test KernelContext with all symbol types populated with specified types.
    /// Arrays are indexed by atom id, e.g., monomorph_types[2] gives type for Monomorph(2).
    #[cfg(test)]
    pub fn test_with_all_types(
        scoped_types: &[ClosedType],
        global_types: &[ClosedType],
        monomorph_types: &[ClosedType],
        synthetic_types: &[ClosedType],
    ) -> KernelContext {
        let mut ctx = KernelContext::new();
        for closed_type in scoped_types {
            ctx.symbol_table.add_scoped_constant(closed_type.clone());
        }
        for closed_type in global_types {
            ctx.symbol_table.add_global_constant(closed_type.clone());
        }
        for closed_type in monomorph_types {
            ctx.symbol_table.add_monomorph(closed_type.clone());
        }
        for closed_type in synthetic_types {
            ctx.symbol_table.declare_synthetic(closed_type.clone());
        }
        ctx
    }

    /// Creates a test KernelContext with function types for testing.
    /// Sets up various function types and assigns them to symbols.
    ///
    /// Symbol type assignments:
    /// - g0, c0: (Bool, Bool) -> Bool
    /// - g1, c1: Bool -> Bool
    /// - g2, c2: (Bool, Bool, Bool) -> Bool
    /// - g3, c3: Empty -> Bool (for tests with EMPTY-typed args)
    /// - g4, c4: (Empty, Empty) -> Empty
    /// - g5-g9, c5-c9: Bool
    #[cfg(test)]
    pub fn test_with_function_types() -> KernelContext {
        use crate::elaborator::acorn_type::{AcornType, FunctionType};

        let mut ctx = KernelContext::new();

        // Add function types and get ClosedTypes
        let bool_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let bool2_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool, AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let bool3_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool, AcornType::Bool, AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let empty_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Empty],
            return_type: Box::new(AcornType::Bool),
        });
        let empty2_to_empty = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Empty, AcornType::Empty],
            return_type: Box::new(AcornType::Empty),
        });
        // Higher-order type like true_below: (Bool -> Bool, Bool) -> Bool
        let func_bool_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![bool_to_bool.clone(), AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        // Type like (Bool -> Bool) -> Bool
        let func_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![bool_to_bool.clone()],
            return_type: Box::new(AcornType::Bool),
        });

        // Register types in the type store first
        ctx.type_store.add_type(&bool_to_bool);
        ctx.type_store.add_type(&bool2_to_bool);
        ctx.type_store.add_type(&bool3_to_bool);
        ctx.type_store.add_type(&empty_to_bool);
        ctx.type_store.add_type(&empty2_to_empty);
        ctx.type_store.add_type(&func_bool_to_bool);
        ctx.type_store.add_type(&func_to_bool);

        let closed_bool_to_bool = ctx
            .type_store
            .get_closed_type(&bool_to_bool)
            .expect("type should be valid");
        let closed_bool2_to_bool = ctx
            .type_store
            .get_closed_type(&bool2_to_bool)
            .expect("type should be valid");
        let closed_bool3_to_bool = ctx
            .type_store
            .get_closed_type(&bool3_to_bool)
            .expect("type should be valid");
        let closed_empty_to_bool = ctx
            .type_store
            .get_closed_type(&empty_to_bool)
            .expect("type should be valid");
        let closed_empty2_to_empty = ctx
            .type_store
            .get_closed_type(&empty2_to_empty)
            .expect("type should be valid");
        let closed_func_bool_to_bool = ctx
            .type_store
            .get_closed_type(&func_bool_to_bool)
            .expect("type should be valid");
        let closed_func_to_bool = ctx
            .type_store
            .get_closed_type(&func_to_bool)
            .expect("type should be valid");

        // Add global constants with function types
        ctx.symbol_table
            .add_global_constant(closed_bool2_to_bool.clone()); // g0
        ctx.symbol_table
            .add_global_constant(closed_bool_to_bool.clone()); // g1
        ctx.symbol_table
            .add_global_constant(closed_bool3_to_bool.clone()); // g2
        ctx.symbol_table
            .add_global_constant(closed_empty_to_bool.clone()); // g3
        ctx.symbol_table
            .add_global_constant(closed_empty2_to_empty.clone()); // g4
        for _ in 5..10 {
            ctx.symbol_table.add_global_constant(ClosedType::bool());
        }
        // h0: (Bool -> Bool, Bool) -> Bool (like true_below)
        ctx.symbol_table
            .add_global_constant(closed_func_bool_to_bool.clone());
        // h1: (Bool -> Bool) -> Bool
        ctx.symbol_table
            .add_global_constant(closed_func_to_bool.clone());

        // Add scoped constants with similar types
        ctx.symbol_table
            .add_scoped_constant(closed_bool2_to_bool.clone()); // c0
        ctx.symbol_table
            .add_scoped_constant(closed_bool_to_bool.clone()); // c1
        ctx.symbol_table
            .add_scoped_constant(closed_bool3_to_bool.clone()); // c2
        ctx.symbol_table
            .add_scoped_constant(closed_empty_to_bool.clone()); // c3
        ctx.symbol_table
            .add_scoped_constant(closed_empty2_to_empty.clone()); // c4
        for _ in 5..10 {
            ctx.symbol_table.add_scoped_constant(ClosedType::bool());
        }

        // Add monomorphs with function types (m0-m4 are functions, m5-m9 are Bool)
        ctx.symbol_table.add_monomorph(closed_bool2_to_bool); // m0
        ctx.symbol_table.add_monomorph(closed_bool_to_bool); // m1
        ctx.symbol_table.add_monomorph(closed_bool3_to_bool); // m2
        ctx.symbol_table.add_monomorph(closed_empty_to_bool); // m3
        ctx.symbol_table.add_monomorph(closed_empty2_to_empty); // m4
        for _ in 5..10 {
            ctx.symbol_table.add_monomorph(ClosedType::bool());
        }

        // Add synthetics with BOOL type
        for _ in 0..10 {
            ctx.symbol_table.declare_synthetic(ClosedType::bool());
        }

        ctx
    }

    /// Add a datatype by name for testing.
    /// Returns self for chaining.
    ///
    /// Example: `ctx.add_datatype("Int")`
    #[cfg(test)]
    pub fn add_datatype(&mut self, name: &str) -> &mut Self {
        use crate::elaborator::acorn_type::{AcornType, Datatype};
        use crate::module::ModuleId;

        let datatype = Datatype {
            module_id: ModuleId(0),
            name: name.to_string(),
        };
        let acorn_type = AcornType::Data(datatype, vec![]);
        self.type_store.add_type(&acorn_type);
        self
    }

    /// Add multiple datatypes by name for testing.
    /// Returns self for chaining.
    ///
    /// Example: `ctx.add_datatypes(&["Int", "Nat", "Real"])`
    #[cfg(test)]
    pub fn add_datatypes(&mut self, names: &[&str]) -> &mut Self {
        for name in names {
            self.add_datatype(name);
        }
        self
    }

    /// Parse a type string like "Bool", "Int", "Int -> Bool", or "(Int, Int) -> Bool".
    /// Looks up datatype names in the TypeStore.
    #[cfg(test)]
    fn parse_type(&self, type_str: &str) -> ClosedType {
        use crate::kernel::types::{GROUND_BOOL, GROUND_EMPTY};

        let s = type_str.trim();

        // Check for arrow type: "A -> B"
        if let Some(arrow_pos) = Self::find_top_level_arrow(s) {
            let input_str = s[..arrow_pos].trim();
            let output_str = s[arrow_pos + 2..].trim();

            let output = self.parse_type(output_str);

            if input_str.starts_with('(') && input_str.ends_with(')') {
                // Multi-argument: "(A, B, C)" -> curried Pi
                let inner = &input_str[1..input_str.len() - 1];
                let args: Vec<&str> = Self::split_by_comma(inner);
                let mut result = output;
                for arg in args.iter().rev() {
                    let arg_type = self.parse_type(arg.trim());
                    result = ClosedType::pi(arg_type, result);
                }
                result
            } else {
                let input = self.parse_type(input_str);
                ClosedType::pi(input, output)
            }
        } else {
            // Simple type name
            match s {
                "Bool" => ClosedType::ground(GROUND_BOOL),
                "Empty" => ClosedType::ground(GROUND_EMPTY),
                _ => {
                    // Look up in TypeStore by name
                    self.type_store
                        .get_ground_id_by_name(s)
                        .map(ClosedType::ground)
                        .unwrap_or_else(|| panic!("Unknown type name: {}", s))
                }
            }
        }
    }

    /// Find the position of a top-level "->" (not inside parentheses).
    #[cfg(test)]
    fn find_top_level_arrow(s: &str) -> Option<usize> {
        let mut depth = 0;
        let bytes = s.as_bytes();
        for i in 0..bytes.len().saturating_sub(1) {
            match bytes[i] {
                b'(' => depth += 1,
                b')' => depth -= 1,
                b'-' if depth == 0 && bytes.get(i + 1) == Some(&b'>') => return Some(i),
                _ => {}
            }
        }
        None
    }

    /// Split a string by commas, respecting parentheses.
    #[cfg(test)]
    fn split_by_comma(s: &str) -> Vec<&str> {
        let mut result = Vec::new();
        let mut depth = 0;
        let mut start = 0;
        for (i, c) in s.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                ',' if depth == 0 => {
                    result.push(&s[start..i]);
                    start = i + 1;
                }
                _ => {}
            }
        }
        result.push(&s[start..]);
        result
    }

    /// Add a constant with a given name and type string for testing.
    /// The name should be like "c0", "g0", "m0", or "s0".
    /// Returns self for chaining.
    ///
    /// Example: `ctx.add_constant("c0", "Int").add_constant("g0", "Int -> Bool")`
    #[cfg(test)]
    pub fn add_constant(&mut self, name: &str, type_str: &str) -> &mut Self {
        let closed_type = self.parse_type(type_str);
        let first_char = name.chars().next().expect("empty constant name");
        let id: u32 = name[1..].parse().expect("invalid constant id");

        match first_char {
            'c' => {
                while self.symbol_table.num_scoped_constants() <= id {
                    self.symbol_table.add_scoped_constant(ClosedType::empty());
                }
                self.symbol_table.set_scoped_constant_type(id, closed_type);
            }
            'g' => {
                while self.symbol_table.num_global_constants() <= id {
                    self.symbol_table.add_global_constant(ClosedType::empty());
                }
                self.symbol_table.set_global_constant_type(id, closed_type);
            }
            'm' => {
                while self.symbol_table.num_monomorphs() <= id {
                    self.symbol_table.add_monomorph(ClosedType::empty());
                }
                self.symbol_table.set_monomorph_type(id, closed_type);
            }
            's' => {
                while self.symbol_table.num_synthetics() <= id {
                    self.symbol_table.declare_synthetic(ClosedType::empty());
                }
                self.symbol_table.set_synthetic_type(id, closed_type);
            }
            _ => panic!("Unknown constant prefix: {}", first_char),
        }
        self
    }

    /// Add multiple constants with the same type for testing.
    /// Returns self for chaining.
    ///
    /// Example: `ctx.add_constants(&["c0", "c1", "c2"], "Int")`
    #[cfg(test)]
    pub fn add_constants(&mut self, names: &[&str], type_str: &str) -> &mut Self {
        for name in names {
            self.add_constant(name, type_str);
        }
        self
    }

    /// Create a LocalContext with variables of the given types.
    /// var_types[i] is the type string for variable x_i.
    ///
    /// Example: `ctx.make_local(&["Int", "Bool"])` creates context where x0: Int, x1: Bool
    #[cfg(test)]
    pub fn make_local(&self, var_types: &[&str]) -> crate::kernel::local_context::LocalContext {
        use crate::kernel::local_context::LocalContext;

        let closed_types: Vec<ClosedType> = var_types
            .iter()
            .map(|type_str| self.parse_type(type_str))
            .collect();
        LocalContext::from_closed_types(closed_types)
    }

    /// Parse a clause string with the given variable types.
    /// var_types[i] is the type string for variable x_i.
    ///
    /// Example: `ctx.make_clause("x0 = c0", &["Int"])` parses clause with x0: Int
    #[cfg(test)]
    pub fn make_clause(
        &self,
        clause_str: &str,
        var_types: &[&str],
    ) -> crate::kernel::clause::Clause {
        use crate::kernel::clause::Clause;

        let local = self.make_local(var_types);
        Clause::old_parse(clause_str, local, self)
    }
}

impl Default for KernelContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::closed_type::ClosedType;
    use crate::kernel::symbol::Symbol;

    #[test]
    fn test_test_with_constants_works() {
        let ctx = KernelContext::test_with_constants(10, 10);
        // Verify we can look up the types for scoped constants c0-c9
        for i in 0..10 {
            let symbol = Symbol::ScopedConstant(i);
            let closed_type = ctx.symbol_table.get_closed_type(symbol);
            assert_eq!(*closed_type, ClosedType::empty());
        }
        // Verify we can look up the types for global constants g0-g9
        for i in 0..10 {
            let symbol = Symbol::GlobalConstant(i);
            let closed_type = ctx.symbol_table.get_closed_type(symbol);
            assert_eq!(*closed_type, ClosedType::empty());
        }
    }

    #[test]
    fn test_add_datatype_and_constant() {
        let mut ctx = KernelContext::new();
        ctx.add_datatype("Int")
            .add_constant("c0", "Int")
            .add_constant("c1", "Int -> Bool")
            .add_constant("c2", "(Int, Int) -> Bool");

        // Verify c0 has type Int
        let c0_type = ctx.symbol_table.get_closed_type(Symbol::ScopedConstant(0));
        let int_id = ctx.type_store.get_ground_id_by_name("Int").unwrap();
        assert_eq!(*c0_type, ClosedType::ground(int_id));

        // Verify c1 has type Int -> Bool
        let c1_type = ctx.symbol_table.get_closed_type(Symbol::ScopedConstant(1));
        assert!(c1_type.as_pi().is_some());

        // Verify c2 has type (Int, Int) -> Bool (curried as Int -> Int -> Bool)
        let c2_type = ctx.symbol_table.get_closed_type(Symbol::ScopedConstant(2));
        let (_, inner) = c2_type.as_pi().unwrap();
        assert!(inner.as_pi().is_some()); // Should be another arrow type
    }
}
