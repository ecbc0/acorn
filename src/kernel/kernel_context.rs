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
