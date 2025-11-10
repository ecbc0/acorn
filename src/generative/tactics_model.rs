use std::error::Error;
use std::fs;
use std::path::Path;
use std::sync::{Arc, OnceLock};

use ndarray::Array2;
use ort::session::builder::GraphOptimizationLevel;
use ort::session::Session;
use rand::Rng;
use tokenizers::Tokenizer;

use crate::ort_utils::ensure_ort_initialized;

// The TacticsModel uses ONNX Runtime to load a generative model for theorem proving.
// This is a BPE-tokenized GPT model that:
// - Input: token indices with shape (batch_size, context_length)
// - Output: logits with shape (batch_size, context_length, vocab_size)
// Unlike ScoringModel, this loads the model from a directory path at runtime.
// The directory should contain: model.onnx, tokenizer.json, and config.json
pub struct TacticsModel {
    // The ONNX model session.
    session: Arc<Session>,
    // The tokenizer for encoding/decoding text
    tokenizer: Tokenizer,
    // Maximum context length (typically 256)
    context_length: usize,
    // Vocabulary size
    vocab_size: usize,
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
    // Loads a model from a directory path at runtime.
    // The directory should contain: model.onnx, tokenizer.json, and config.json
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn Error>> {
        let dir_path = path.as_ref();

        // Load the ONNX model
        let model_path = dir_path.join("model.onnx");
        let bytes = fs::read(&model_path)?;
        let session = TACTICS_SESSION.get_or_init(|| {
            make_session(&bytes).expect("Failed to initialize tactics model session")
        });

        // Load the tokenizer
        let tokenizer_path = dir_path.join("tokenizer.json");
        let tokenizer = Tokenizer::from_file(&tokenizer_path)
            .map_err(|e| format!("Failed to load tokenizer: {}", e))?;

        // Load config to get vocab_size
        let config_path = dir_path.join("config.json");
        let config_str = fs::read_to_string(&config_path)?;
        let config: serde_json::Value = serde_json::from_str(&config_str)?;
        let vocab_size = config["vocab_size"]
            .as_u64()
            .ok_or("vocab_size not found in config.json")? as usize;
        let context_length = config["context_length"]
            .as_u64()
            .ok_or("context_length not found in config.json")?
            as usize;

        Ok(TacticsModel {
            session: Arc::clone(session),
            tokenizer,
            context_length,
            vocab_size,
        })
    }

    /// Encodes a string prompt into token indices using the BPE tokenizer
    pub fn encode(&self, prompt: &str) -> Vec<i64> {
        let encoding = self.tokenizer.encode(prompt, false).unwrap();
        encoding.get_ids().iter().map(|&id| id as i64).collect()
    }

    /// Decodes token indices back into a string using the BPE tokenizer
    pub fn decode(&self, tokens: &[i64]) -> String {
        let ids: Vec<u32> = tokens.iter().map(|&t| t as u32).collect();
        self.tokenizer.decode(&ids, true).unwrap_or_default()
    }

    /// Runs inference on a prompt and returns logits
    /// Input shape: (1, context_length)
    /// Output shape: (1, context_length, vocab_size)
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

        // Extract output tensor (1, context_length, vocab_size)
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
            .to_shape((1, self.vocab_size))?
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

        // Fallback to last token in vocab
        (self.vocab_size - 1) as i64
    }

    /// Simple text generation (for testing)
    pub fn generate_simple(
        &self,
        prompt: &str,
        max_tokens: usize,
        temperature: f32,
    ) -> Result<String, Box<dyn Error>> {
        let mut current_tokens = self.encode(prompt);
        let mut generated_tokens = Vec::new();

        for _ in 0..max_tokens {
            // Truncate to context length if needed
            let start = if current_tokens.len() > self.context_length {
                current_tokens.len() - self.context_length
            } else {
                0
            };
            let context_prompt = self.decode(&current_tokens[start..]);

            let logits = self.infer(&context_prompt)?;
            let next_token = self.sample_token(&logits, temperature);

            generated_tokens.push(next_token);
            current_tokens.push(next_token);
        }

        Ok(self.decode(&generated_tokens))
    }

    /// Generate a single line of text, stopping at newline or max_tokens
    /// Returns the generated text without the trailing newline
    pub fn generate_line(
        &self,
        prompt: &str,
        max_tokens: usize,
        temperature: f32,
    ) -> Result<String, Box<dyn Error>> {
        let mut current_tokens = self.encode(prompt);
        let mut generated_tokens = Vec::new();

        for _ in 0..max_tokens {
            // Truncate to context length if needed
            let start = if current_tokens.len() > self.context_length {
                current_tokens.len() - self.context_length
            } else {
                0
            };
            let context_prompt = self.decode(&current_tokens[start..]);

            let logits = self.infer(&context_prompt)?;
            let next_token = self.sample_token(&logits, temperature);

            // Check if this token contains a newline
            let token_text = self.decode(&[next_token]);
            if token_text.contains('\n') {
                // Don't include the newline in the generated tokens
                break;
            }

            generated_tokens.push(next_token);
            current_tokens.push(next_token);
        }

        Ok(self.decode(&generated_tokens))
    }

    pub fn context_length(&self) -> usize {
        self.context_length
    }

    pub fn vocab_size(&self) -> usize {
        self.vocab_size
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
