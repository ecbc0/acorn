pub mod aliases;
pub mod atom;
pub mod clause;
pub mod clause_set;
pub mod closed_type;
pub mod cnf;
pub mod display;
pub mod extended_term;
pub mod fingerprint;
pub mod inference;
pub mod kernel_context;
pub mod literal;
pub mod local_context;
pub mod new_term_graph;
pub mod pattern_tree;
pub mod symbol;
pub mod symbol_table;
pub mod term;
pub mod term_graph;
pub mod trace;
pub mod type_store;
pub mod types;
pub mod unifier;
pub mod variable_map;

// Re-export the appropriate TermGraph implementation based on feature flag.
// StepId, RewriteSource, and RewriteStep are shared between both implementations.
#[cfg(not(feature = "new_term_graph"))]
pub use term_graph::{
    OldTermGraph as TermGraph, OldTermGraphContradiction as TermGraphContradiction, RewriteSource,
    RewriteStep, StepId,
};

#[cfg(feature = "new_term_graph")]
pub use new_term_graph::{
    NewTermGraph as TermGraph, NewTermGraphContradiction as TermGraphContradiction, RewriteSource,
    RewriteStep, StepId,
};
