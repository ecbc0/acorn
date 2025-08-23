/// A proof certificate containing the concrete proof steps
pub struct Certificate {
    /// The name of the goal that was proved
    pub goal: String,
    /// The proof steps as strings
    pub proof: Vec<String>,
}

impl Certificate {
    /// Create a new certificate from proof steps
    pub fn new(goal: String, proof: Vec<String>) -> Self {
        Certificate { goal, proof }
    }
}