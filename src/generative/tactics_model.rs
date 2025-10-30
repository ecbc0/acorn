use std::error::Error;
use std::fs;
use std::path::Path;
use std::sync::{Arc, OnceLock};

use ort::session::builder::GraphOptimizationLevel;
use ort::session::Session;

use crate::ort_utils::ensure_ort_initialized;

// The TacticsModel uses ONNX Runtime to load a generative model for theorem proving.
// Unlike ScoringModel, this loads the model from a file path at runtime.
pub struct TacticsModel {
    // The ONNX model session.
    session: Arc<Session>,
}

static TACTICS_SESSION: OnceLock<Arc<Session>> = OnceLock::new();

fn make_session(bytes: &[u8]) -> Result<Arc<Session>, Box<dyn Error>> {
    ensure_ort_initialized()?;

    let session = Session::builder()?
        .with_intra_threads(1)?
        .with_inter_threads(1)?
        .with_optimization_level(GraphOptimizationLevel::Level3)?
        .commit_from_memory(bytes)?;
    Ok(Arc::new(session))
}

impl TacticsModel {
    // Loads a model from a file path at runtime.
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn Error>> {
        let bytes = fs::read(path.as_ref())?;
        let session = TACTICS_SESSION.get_or_init(|| {
            make_session(&bytes).expect("Failed to initialize tactics model session")
        });
        Ok(TacticsModel {
            session: Arc::clone(session),
        })
    }

    // Placeholder method for generating tactics.
    // This will be expanded based on the actual model's input/output format.
    pub fn generate(&self) -> Result<(), Box<dyn Error>> {
        // TODO: Implement actual generation logic based on model architecture
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tactics_model_placeholder() {
        // This is a placeholder test. Actual tests will depend on having a model file.
        // For now, we just ensure the module compiles.
        assert!(true);
    }
}
