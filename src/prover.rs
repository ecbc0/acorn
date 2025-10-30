/// Mode controlling proof search behavior
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProverMode {
    /// About as long as a human is willing to wait for a proof.
    Interactive,

    /// A fast search that only uses shallow steps, for testing.
    Test,
}
