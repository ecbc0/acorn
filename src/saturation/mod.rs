pub mod active_set;
pub mod dataset;
pub mod features;
pub mod fingerprint;
pub mod passive_set;
pub mod proof;
pub mod prover;
pub mod rewrite_tree;
pub mod score;
pub mod scorer;
pub mod scoring_model;

// Re-export the main public types
pub use prover::SaturationProver;
