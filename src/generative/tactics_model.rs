use std::error::Error;
use std::fs;
use std::path::Path;
use std::sync::{Arc, OnceLock};

use ndarray::Array2;
use ort::session::builder::GraphOptimizationLevel;
use ort::session::Session;
use rand::Rng;

use crate::ort_utils::ensure_ort_initialized;

// The TacticsModel uses ONNX Runtime to load a generative model for theorem proving.
// This is a character-level GPT model that:
// - Input: token indices (bytes 0-255) with shape (batch_size, context_length)
// - Output: logits with shape (batch_size, context_length, vocab_size=256)
// Unlike ScoringModel, this loads the model from a file path at runtime.
pub struct TacticsModel {
    // The ONNX model session.
    session: Arc<Session>,
    // Maximum context length (typically 512)
    context_length: usize,
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

        // Extract context length from model input shape
        // Input shape is typically [batch_size, context_length]
        let input_shape = session.inputs[0]
            .input_type
            .tensor_dimensions()
            .ok_or("No input dimensions")?;
        let context_length = match input_shape.get(1) {
            Some(&dim) => dim as usize,
            _ => return Err("Could not determine context length from model".into()),
        };

        Ok(TacticsModel {
            session: Arc::clone(session),
            context_length,
        })
    }

    /// Encodes a string prompt into token indices (byte-level encoding)
    pub fn encode(&self, prompt: &str) -> Vec<i64> {
        prompt.bytes().map(|b| b as i64).collect()
    }

    /// Decodes token indices back into a string
    pub fn decode(&self, tokens: &[i64]) -> String {
        tokens
            .iter()
            .filter_map(|&t| {
                if t >= 0 && t < 256 {
                    Some(t as u8 as char)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Runs inference on a prompt and returns logits
    /// Input shape: (1, context_length)
    /// Output shape: (1, context_length, 256)
    pub fn infer(&self, prompt: &str) -> Result<Array2<f32>, Box<dyn Error>> {
        let tokens = self.encode(prompt);

        // Pad or truncate to context length
        let mut input_tokens = vec![0i64; self.context_length];
        let copy_len = tokens.len().min(self.context_length);
        input_tokens[..copy_len].copy_from_slice(&tokens[..copy_len]);

        // Create input array (1, context_length)
        let input_array = Array2::from_shape_vec((1, self.context_length), input_tokens)?;

        // Run inference
        let inputs = ort::inputs![input_array]?;
        let outputs = self.session.run(inputs)?;

        // Extract output tensor (1, context_length, 256)
        let output = outputs[0].try_extract_tensor::<f32>()?;
        let shape = output.shape();

        if shape.len() != 3 {
            return Err(format!("Expected 3D output, got shape {:?}", shape).into());
        }

        // Get the last position's logits (for next token prediction)
        let last_pos = copy_len.saturating_sub(1);
        let logits = output
            .slice(ndarray::s![0, last_pos, ..])
            .to_owned()
            .to_shape((1, 256))?
            .to_owned();

        Ok(logits)
    }

    /// Generate a single next token by sampling from logits
    pub fn sample_token(&self, logits: &Array2<f32>, temperature: f32) -> i64 {
        // Apply temperature
        let scaled_logits: Vec<f32> = logits.row(0).iter().map(|&x| x / temperature).collect();

        // Compute softmax
        let max_logit = scaled_logits
            .iter()
            .copied()
            .fold(f32::NEG_INFINITY, f32::max);
        let exp_logits: Vec<f32> = scaled_logits
            .iter()
            .map(|&x| (x - max_logit).exp())
            .collect();
        let sum_exp: f32 = exp_logits.iter().sum();
        let probs: Vec<f32> = exp_logits.iter().map(|&x| x / sum_exp).collect();

        // Sample from distribution
        let mut cumsum = 0.0;
        let random_value: f32 = rand::thread_rng().gen();

        for (i, &p) in probs.iter().enumerate() {
            cumsum += p;
            if random_value <= cumsum {
                return i as i64;
            }
        }

        // Fallback
        255
    }

    /// Simple text generation (for testing)
    pub fn generate_simple(
        &self,
        prompt: &str,
        max_tokens: usize,
        temperature: f32,
    ) -> Result<String, Box<dyn Error>> {
        let mut current_prompt = prompt.to_string();
        let mut generated = String::new();

        for _ in 0..max_tokens {
            let logits = self.infer(&current_prompt)?;
            let next_token = self.sample_token(&logits, temperature);

            let next_char = (next_token as u8) as char;
            generated.push(next_char);
            current_prompt.push(next_char);

            // Keep only last context_length chars
            if current_prompt.len() > self.context_length {
                current_prompt =
                    current_prompt[current_prompt.len() - self.context_length..].to_string();
            }
        }

        Ok(generated)
    }

    pub fn context_length(&self) -> usize {
        self.context_length
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_tactics_model_placeholder() {
        // This is a placeholder test. Actual tests will depend on having a model file.
        // For now, we just ensure the module compiles.
        assert!(true);
    }
}
