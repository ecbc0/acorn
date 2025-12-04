use std::sync::LazyLock;

#[cfg(test)]
use crate::kernel::fat_term::{TypeId, EMPTY};
use crate::kernel::symbol_table::SymbolTable;
use crate::kernel::type_store::TypeStore;

/// KernelContext combines the TypeStore and SymbolTable that are needed
/// for working with thin types and various kernel operations.
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

    /// Returns a reference to a fake empty KernelContext.
    /// Use this when working with FatTerm/FatClause that don't actually need the context.
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
            ctx.symbol_table.add_scoped_constant_with_type(EMPTY);
        }
        ctx
    }

    /// Creates a test KernelContext with pre-populated scoped constants with specified types.
    #[cfg(test)]
    pub fn test_with_scoped_constant_types(types: &[TypeId]) -> KernelContext {
        let mut ctx = KernelContext::new();
        for &type_id in types {
            ctx.symbol_table.add_scoped_constant_with_type(type_id);
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
            ctx.symbol_table.add_scoped_constant_with_type(EMPTY);
        }
        for _ in 0..num_global {
            ctx.symbol_table.add_global_constant_with_type(EMPTY);
        }
        // Also add monomorphs for tests that use "m0", "m1", etc.
        for _ in 0..10 {
            ctx.symbol_table.add_monomorph_with_type(EMPTY);
        }
        // Also add synthetics for tests that use "s0", "s1", etc.
        for _ in 0..10 {
            ctx.symbol_table.declare_synthetic(EMPTY);
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
        use crate::kernel::fat_term::BOOL;

        let mut ctx = KernelContext::new();

        // Create a (Bool, Bool) -> Bool function type for monomorphs
        let bool2_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool, AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let type_bool2_to_bool = ctx.type_store.add_type(&bool2_to_bool);

        // Scoped and global constants are Bool
        for _ in 0..10 {
            ctx.symbol_table.add_scoped_constant_with_type(BOOL);
        }
        for _ in 0..10 {
            ctx.symbol_table.add_global_constant_with_type(BOOL);
        }

        // Monomorphs are (Bool, Bool) -> Bool functions
        for _ in 0..10 {
            ctx.symbol_table.add_monomorph_with_type(type_bool2_to_bool);
        }

        // Synthetics are Bool
        for _ in 0..10 {
            ctx.symbol_table.declare_synthetic(BOOL);
        }
        ctx
    }

    /// Creates a test KernelContext with pre-populated scoped and global constants with
    /// specified types.
    /// For use in tests that load FatClauses from JSON with specific type requirements.
    #[cfg(test)]
    pub fn test_with_constant_types(
        scoped_types: &[TypeId],
        global_types: &[TypeId],
    ) -> KernelContext {
        let mut ctx = KernelContext::new();
        for &type_id in scoped_types {
            ctx.symbol_table.add_scoped_constant_with_type(type_id);
        }
        for &type_id in global_types {
            ctx.symbol_table.add_global_constant_with_type(type_id);
        }
        ctx
    }

    /// Creates a test KernelContext with all symbol types populated with specified types.
    /// Arrays are indexed by atom id, e.g., monomorph_types[2] gives type for Monomorph(2).
    #[cfg(test)]
    pub fn test_with_all_types(
        scoped_types: &[TypeId],
        global_types: &[TypeId],
        monomorph_types: &[TypeId],
        synthetic_types: &[TypeId],
    ) -> KernelContext {
        let mut ctx = KernelContext::new();
        for &type_id in scoped_types {
            ctx.symbol_table.add_scoped_constant_with_type(type_id);
        }
        for &type_id in global_types {
            ctx.symbol_table.add_global_constant_with_type(type_id);
        }
        for &type_id in monomorph_types {
            ctx.symbol_table.add_monomorph_with_type(type_id);
        }
        for &type_id in synthetic_types {
            ctx.symbol_table.declare_synthetic(type_id);
        }
        ctx
    }

    /// Creates a test KernelContext with function types for testing.
    /// Sets up various function types and assigns them to symbols.
    ///
    /// Function types created:
    /// - TypeId(2): Bool -> Bool
    /// - TypeId(3): (Bool, Bool) -> Bool  (curried as Bool -> (Bool -> Bool))
    /// - TypeId(4): (Bool, Bool, Bool) -> Bool
    /// - TypeId(5): Empty -> Bool
    /// - TypeId(6): (Empty, Empty) -> Empty
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
        use crate::kernel::fat_term::BOOL;

        let mut ctx = KernelContext::new();

        // Add function types
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

        let type_bool_to_bool = ctx.type_store.add_type(&bool_to_bool);
        let type_bool2_to_bool = ctx.type_store.add_type(&bool2_to_bool);
        let type_bool3_to_bool = ctx.type_store.add_type(&bool3_to_bool);
        let type_empty_to_bool = ctx.type_store.add_type(&empty_to_bool);
        let type_empty2_to_empty = ctx.type_store.add_type(&empty2_to_empty);

        // Add global constants with function types
        ctx.symbol_table
            .add_global_constant_with_type(type_bool2_to_bool); // g0
        ctx.symbol_table
            .add_global_constant_with_type(type_bool_to_bool); // g1
        ctx.symbol_table
            .add_global_constant_with_type(type_bool3_to_bool); // g2
        ctx.symbol_table
            .add_global_constant_with_type(type_empty_to_bool); // g3
        ctx.symbol_table
            .add_global_constant_with_type(type_empty2_to_empty); // g4
        for _ in 5..10 {
            ctx.symbol_table.add_global_constant_with_type(BOOL);
        }

        // Add scoped constants with similar types
        ctx.symbol_table
            .add_scoped_constant_with_type(type_bool2_to_bool); // c0
        ctx.symbol_table
            .add_scoped_constant_with_type(type_bool_to_bool); // c1
        ctx.symbol_table
            .add_scoped_constant_with_type(type_bool3_to_bool); // c2
        ctx.symbol_table
            .add_scoped_constant_with_type(type_empty_to_bool); // c3
        ctx.symbol_table
            .add_scoped_constant_with_type(type_empty2_to_empty); // c4
        for _ in 5..10 {
            ctx.symbol_table.add_scoped_constant_with_type(BOOL);
        }

        // Add monomorphs with function types (m0-m4 are functions, m5-m9 are Bool)
        ctx.symbol_table.add_monomorph_with_type(type_bool2_to_bool); // m0
        ctx.symbol_table.add_monomorph_with_type(type_bool_to_bool); // m1
        ctx.symbol_table.add_monomorph_with_type(type_bool3_to_bool); // m2
        ctx.symbol_table.add_monomorph_with_type(type_empty_to_bool); // m3
        ctx.symbol_table
            .add_monomorph_with_type(type_empty2_to_empty); // m4
        for _ in 5..10 {
            ctx.symbol_table.add_monomorph_with_type(BOOL);
        }

        // Add synthetics with BOOL type
        for _ in 0..10 {
            ctx.symbol_table.declare_synthetic(BOOL);
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
    use crate::kernel::symbol::Symbol;

    #[test]
    fn test_test_with_constants_works() {
        let ctx = KernelContext::test_with_constants(10, 10);
        // Verify we can look up the types for scoped constants c0-c9
        for i in 0..10 {
            let symbol = Symbol::ScopedConstant(i);
            let type_id = ctx.symbol_table.get_type(symbol);
            assert_eq!(type_id, EMPTY);
        }
        // Verify we can look up the types for global constants g0-g9
        for i in 0..10 {
            let symbol = Symbol::GlobalConstant(i);
            let type_id = ctx.symbol_table.get_type(symbol);
            assert_eq!(type_id, EMPTY);
        }
    }
}
