use std::fmt;

use crate::binding_map::BindingMap;
use crate::certificate::Certificate;
use crate::code_generator::Error;
use crate::goal::Goal;
use crate::normalizer::{NormalizedGoal, Normalizer};
use crate::project::Project;
use crate::proof_step::ProofStep;

/// Mode controlling proof search behavior
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProverMode {
    /// About as long as a human is willing to wait for a proof.
    Interactive,

    /// A fast search that only uses shallow steps, for testing.
    Test,
}

/// The outcome of a proof search
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Success,
    Exhausted,
    Inconsistent,
    Interrupted,
    Timeout,
    Constrained,
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Outcome::Success => write!(f, "Success"),
            Outcome::Exhausted => write!(f, "Exhausted"),
            Outcome::Inconsistent => write!(f, "Inconsistent"),
            Outcome::Interrupted => write!(f, "Interrupted"),
            Outcome::Timeout => write!(f, "Timeout"),
            Outcome::Constrained => write!(f, "Constrained"),
        }
    }
}

/// A trait for theorem provers
pub trait Prover: Clone {
    /// Add proof steps to the prover (facts or axioms)
    fn add_steps(&mut self, steps: Vec<ProofStep>);

    /// Set the goal and add goal-derived steps
    fn set_goal(
        &mut self,
        goal: NormalizedGoal,
        steps: Vec<ProofStep>,
        project: &Project,
        original_goal: &Goal,
    );

    /// Run the proof search with the given mode
    fn search(&mut self, mode: ProverMode) -> Outcome;

    /// Generate a certificate for the proof
    fn make_cert(
        &self,
        project: &Project,
        bindings: &BindingMap,
        normalizer: &Normalizer,
        print: bool,
    ) -> Result<Certificate, Error>;
}
