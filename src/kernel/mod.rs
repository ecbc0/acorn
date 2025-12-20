pub mod atom;
pub mod clause;
pub mod clause_set;
pub mod cnf;
pub mod display;
pub mod equality_graph;
pub mod extended_term;
pub mod fingerprint;
pub mod generalization_set;
pub mod inference;
pub mod kernel_context;
pub mod literal;
pub mod local_context;
pub mod pdt;
pub mod symbol;
pub mod symbol_table;
pub mod term;
pub mod trace;
pub mod type_store;
pub mod types;
pub mod unifier;
pub mod variable_map;

pub use equality_graph::{
    EqualityGraph, EqualityGraphContradiction, RewriteSource, RewriteStep, StepId,
};
