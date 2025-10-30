use std::fmt;

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
