use std::sync::LazyLock;

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

    /// Returns a reference to a fake empty KernelContext.
    pub fn fake() -> &'static KernelContext {
        static FAKE_KERNEL_CONTEXT: LazyLock<KernelContext> = LazyLock::new(KernelContext::new);
        &FAKE_KERNEL_CONTEXT
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
}
