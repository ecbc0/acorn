use crate::builder::BuildError;
use crate::fact::Fact;
use crate::goal::Goal;
use crate::normalizer::Normalizer;
use crate::prover::Prover;

/// The processor represents all of the stuff that can accept a stream of facts.
/// We might want to rename this or refactor it away later.
/// At the time of writing this comment, its primary motivation for existing is
/// to handle the yaml -> jsonl build migration.
#[derive(Clone)]
pub struct Processor {
    pub prover: Prover,
    pub normalizer: Normalizer,
}

impl Processor {
    /// Normalizes a fact and adds the resulting proof steps to the prover.
    pub fn add_fact(&mut self, fact: Fact) -> Result<(), BuildError> {
        let steps = self.normalizer.normalize_fact(fact)?;
        self.prover.add_steps(steps);
        Ok(())
    }

    /// Normalizes a goal and sets it as the prover's goal.
    pub fn set_goal(&mut self, goal: &Goal) -> Result<(), BuildError> {
        let (ng, steps) = self.normalizer.normalize_goal(goal)?;
        self.prover.set_goal(ng, steps);
        Ok(())
    }
}
