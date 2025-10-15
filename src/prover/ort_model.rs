use std::error::Error;
use std::sync::{Arc, OnceLock};

use ndarray::{Axis, IxDyn};
use ort::execution_providers::CPUExecutionProvider;
use ort::session::builder::GraphOptimizationLevel;
use ort::session::Session;

use super::features::Features;
use super::scorer::Scorer;

// The OrtModel uses ort to load an onnx model and uses it to score feature vectors.
pub struct OrtModel {
    // The ONNX model.
    session: Arc<Session>,
}

static GLOBAL_SESSION: OnceLock<Arc<Session>> = OnceLock::new();

const MODEL_BYTES: &[u8] = include_bytes!("../../files/models/model-2024-09-25-15-33-10.onnx");

fn make_session(bytes: &[u8]) -> Result<Arc<Session>, Box<dyn Error>> {
    ort::init()
        .with_execution_providers([CPUExecutionProvider::default().build().error_on_failure()])
        .commit()?;

    let session = Session::builder()?
        .with_intra_threads(1)?
        .with_inter_threads(1)?
        .with_optimization_level(GraphOptimizationLevel::Level3)?
        .commit_from_memory(bytes)?;
    Ok(Arc::new(session))
}

impl OrtModel {
    // Loads a model from bytes.
    // The bytes are typically preloaded into the binary with include_bytes!.
    fn load_bytes(bytes: &[u8]) -> Result<Self, Box<dyn Error>> {
        let session = GLOBAL_SESSION
            .get_or_init(|| make_session(bytes).expect("Failed to initialize ORT session"));
        Ok(OrtModel {
            session: Arc::clone(session),
        })
    }

    // Loads the hardcoded model.
    pub fn load() -> Result<Self, Box<dyn Error>> {
        OrtModel::load_bytes(MODEL_BYTES)
    }
}

impl Scorer for OrtModel {
    // This assumes that the model is calculating a probability of the positive class,
    // where the positive class is a step that was actually taken in a proof.
    // There's a lot of unwrapping - it would be nice to handle errors more gracefully.
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>> {
        let array = features.to_array().insert_axis(Axis(0));
        let inputs = ort::inputs![array]?;
        let outputs = self.session.run(inputs)?;
        let extracted = outputs[0].try_extract_tensor::<f32>()?;
        let ix = IxDyn(&[0, 0]);
        if let Some(score) = extracted.get(ix) {
            Ok(*score)
        } else {
            Err("No score at [0, 0]. Maybe the model is the wrong shape?".into())
        }
    }

    fn score_batch(&self, features: &[Features]) -> Result<Vec<f32>, Box<dyn Error>> {
        let array = Features::to_array2(features);
        let inputs = ort::inputs![array]?;
        let outputs = self.session.run(inputs)?;
        let extracted = outputs[0].try_extract_tensor::<f32>()?;
        let scores: Vec<f32> = extracted.iter().copied().collect();
        Ok(scores)
    }
}

#[cfg(test)]
mod tests {
    use crate::proof_step::ProofStep;

    use super::*;

    #[test]
    fn test_ort_model_score() {
        let step = ProofStep::mock("c0(c3) = c2");
        let features = Features::new(&step);

        // First ort
        let ort_model = OrtModel::load().unwrap();
        let ort_score = ort_model.score(&features).unwrap();
        assert!(ort_score.is_finite());
    }

    #[test]
    fn test_ort_model_batch_score() {
        let step1 = ProofStep::mock("c0(c3) = c2");
        let features1 = Features::new(&step1);
        let step2 = ProofStep::mock("c4(c1, c1) = c4(c2, c2)");
        let features2 = Features::new(&step2);
        let ort_model = OrtModel::load().unwrap();

        let score1 = ort_model.score(&features1).unwrap();
        let score2 = ort_model.score(&features2).unwrap();

        // The scores should be different, even up to floating point error
        assert!((score1 - score2).abs() > 1e-6);

        // Recalculate the scores in a batch
        let scores = ort_model.score_batch(&[features1, features2]).unwrap();
        assert_eq!(scores.len(), 2);
        assert!((scores[0] - score1).abs() < 1e-6);
        assert!((scores[1] - score2).abs() < 1e-6);
    }
}
