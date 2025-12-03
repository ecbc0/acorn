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
}

impl Default for KernelContext {
    fn default() -> Self {
        Self::new()
    }
}
