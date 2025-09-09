use crate::builder::Builder;
use crate::normalizer::Normalizer;
use crate::prover::Prover;

/// The processor represents all of the stuff that can accept a stream of facts.
/// We might want to rename this or refactor it away later.
/// At the time of writing this comment, its primary motivation for existing is
/// to handle the yaml -> jsonl build migration.
pub struct Processor<'a> {
    pub builder: &'a Builder<'a>,
    pub prover: Prover,
    pub normalizer: Normalizer,
}
