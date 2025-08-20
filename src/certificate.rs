/// A proof certificate containing the concrete proof steps
pub struct Certificate {
    /// The proof steps as strings
    pub proof: Vec<String>,
}

impl Certificate {
    /// Create a new certificate from proof steps
    pub fn new(proof: Vec<String>) -> Self {
        Certificate { proof }
    }
}