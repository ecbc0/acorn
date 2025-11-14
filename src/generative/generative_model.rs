use std::error::Error;
use std::fs;
use std::path::Path;
use std::sync::{Arc, OnceLock};

use ndarray::{Array2, Array4};
use ort::session::builder::GraphOptimizationLevel;
use ort::session::Session;
use rand::Rng;
use tokenizers::Tokenizer;

use crate::ort_utils::ensure_ort_initialized;

// The GenerativeModel uses ONNX Runtime to load a generative model for theorem proving.
// This is a BPE-tokenized GPT model that:
// - Input: token indices with shape (batch_size, context_length)
// - Output: logits with shape (batch_size, context_length, vocab_size)
// Unlike ScoringModel, this loads the model from a directory path at runtime.
// The directory should contain: model.onnx, tokenizer.json, and config.json
#[derive(Clone)]
pub struct GenerativeModel {
    // The ONNX model session.
    session: Arc<Session>,
    // The tokenizer for encoding/decoding text
    tokenizer: Arc<Tokenizer>,
    // Maximum context length (typically 256)
    context_length: usize,
    // Vocabulary size
    vocab_size: usize,
    // Number of transformer layers
    n_layers: usize,
    // Number of attention heads
    n_heads: usize,
    // Dimension per attention head
    head_dim: usize,
}

static GENERATIVE_MODEL: OnceLock<Arc<GenerativeModel>> = OnceLock::new();
static GENERATIVE_MODEL_PATH: OnceLock<String> = OnceLock::new();

fn make_session(bytes: &[u8]) -> Result<Arc<Session>, Box<dyn Error>> {
    ensure_ort_initialized()?;

    let session = Session::builder()?
        .with_intra_threads(1)?
        .with_inter_threads(1)?
        .with_optimization_level(GraphOptimizationLevel::Level3)?
        .commit_from_memory(bytes)?;
    Ok(Arc::new(session))
}

impl GenerativeModel {
    // Loads a model from a directory path at runtime.
    // The directory should contain: model.onnx, tokenizer.json, and config.json
    // This can only be called once - subsequent calls with a different path will panic.
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn Error>> {
        let dir_path = path.as_ref();
        let path_str = dir_path.to_string_lossy().to_string();

        // Check if we've already loaded a model
        if let Some(cached_path) = GENERATIVE_MODEL_PATH.get() {
            if cached_path != &path_str {
                panic!(
                    "GenerativeModel::load called with different path. First: {}, Second: {}",
                    cached_path, path_str
                );
            }
            // Return a clone of the cached model
            return Ok((**GENERATIVE_MODEL.get().unwrap()).clone());
        }

        // Load the ONNX model
        let model_path = dir_path.join("model.onnx");
        let bytes = fs::read(&model_path)?;
        let session = make_session(&bytes)?;

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
        let n_layers = config["n_layers"]
            .as_u64()
            .ok_or("n_layers not found in config.json")? as usize;
        let n_heads = config["n_heads"]
            .as_u64()
            .ok_or("n_heads not found in config.json")? as usize;
        let head_dim = config["head_dim"]
            .as_u64()
            .ok_or("head_dim not found in config.json")? as usize;

        let model = GenerativeModel {
            session,
            tokenizer: Arc::new(tokenizer),
            context_length,
            vocab_size,
            n_layers,
            n_heads,
            head_dim,
        };

        // Cache the path and model
        GENERATIVE_MODEL_PATH.set(path_str).ok();
        let cached = GENERATIVE_MODEL.get_or_init(|| Arc::new(model.clone()));
        Ok((**cached).clone())
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

    /// Generate a single line of text, stopping at newline or max_tokens
    /// Returns the generated text without the trailing newline
    pub fn generate_line(
        &self,
        prompt: &str,
        max_tokens: usize,
        temperature: f32,
    ) -> Result<String, Box<dyn Error>> {
        let prompt_tokens = self.encode(prompt);
        let mut cache = GenerationCache::empty(self.n_layers, self.n_heads, self.head_dim);

        // Process prompt tokens one by one to build cache
        for &token in &prompt_tokens {
            self.infer_with_cache(token, &mut cache)?;
        }

        // Generate new tokens
        let mut generated_tokens = Vec::new();
        let mut last_token = *prompt_tokens.last().unwrap_or(&0);

        for _ in 0..max_tokens {
            let logits = self.infer_with_cache(last_token, &mut cache)?;
            let next_token = self.sample_token(&logits, temperature);

            // Check for newline
            let token_text = self.decode(&[next_token]);
            if token_text.contains('\n') {
                break;
            }

            generated_tokens.push(next_token);
            last_token = next_token;
        }

        Ok(self.decode(&generated_tokens))
    }

    pub fn context_length(&self) -> usize {
        self.context_length
    }

    pub fn vocab_size(&self) -> usize {
        self.vocab_size
    }

    pub fn n_layers(&self) -> usize {
        self.n_layers
    }

    pub fn n_heads(&self) -> usize {
        self.n_heads
    }

    pub fn head_dim(&self) -> usize {
        self.head_dim
    }

    /// Generate a single line of text using an existing cache, stopping at newline or max_tokens
    /// This allows the cache to be pre-populated with a prefix for efficient generation
    /// Returns the generated text without the trailing newline
    pub fn generate_line_with_cache(
        &self,
        cache: &mut GenerationCache,
        max_tokens: usize,
        temperature: f32,
    ) -> Result<String, Box<dyn Error>> {
        let mut generated_tokens = Vec::new();

        // We need a starting token to generate from
        // For now, we'll use a newline token as a separator if the cache is non-empty
        // If there's context in the cache, we assume the last generated token is part of it
        // So we just start generating fresh tokens
        let newline_tokens = self.encode("\n");
        let mut last_token = *newline_tokens.first().unwrap_or(&0);

        for _ in 0..max_tokens {
            let logits = self.infer_with_cache(last_token, cache)?;
            let next_token = self.sample_token(&logits, temperature);

            // Check for newline
            let token_text = self.decode(&[next_token]);
            if token_text.contains('\n') {
                break;
            }

            generated_tokens.push(next_token);
            last_token = next_token;
        }

        Ok(self.decode(&generated_tokens))
    }

    /// Run inference for a single token using KV cache
    /// Returns logits for the next token
    pub fn infer_with_cache(
        &self,
        token: i64,
        cache: &mut GenerationCache,
    ) -> Result<Array2<f32>, Box<dyn Error>> {
        use ort::value::{DynValue, Value};

        // Create single-token input (1, 1)
        let input_array = Array2::from_shape_vec((1, 1), vec![token])?;

        // Build the inputs using DynValue to handle different tensor types
        let mut inputs = vec![(
            "input_ids",
            DynValue::from(Value::from_array(input_array.view())?),
        )];

        // Add all past_key_values to inputs
        for (layer_idx, (past_k, past_v)) in cache.layer_caches.iter().enumerate() {
            let k_name = format!("past_key_values.{}.key", layer_idx);
            let v_name = format!("past_key_values.{}.value", layer_idx);

            inputs.push((
                k_name.leak() as &str,
                DynValue::from(Value::from_array(past_k.view())?),
            ));
            inputs.push((
                v_name.leak() as &str,
                DynValue::from(Value::from_array(past_v.view())?),
            ));
        }

        // Run inference
        let outputs = self.session.run(inputs)?;

        // Extract logits
        let logits = outputs["logits"].try_extract_tensor::<f32>()?;

        // Update cache with present_key_values
        for layer_idx in 0..self.n_layers {
            let present_k_dyn = outputs[format!("present_key_values.{}.key", layer_idx).as_str()]
                .try_extract_tensor::<f32>()?;
            let present_v_dyn = outputs[format!("present_key_values.{}.value", layer_idx).as_str()]
                .try_extract_tensor::<f32>()?;

            // Convert from dynamic dimension to fixed Array4
            let shape = present_k_dyn.shape();
            let present_k = present_k_dyn
                .to_owned()
                .to_shape((shape[0], shape[1], shape[2], shape[3]))?
                .to_owned();
            let present_v = present_v_dyn
                .to_owned()
                .to_shape((shape[0], shape[1], shape[2], shape[3]))?
                .to_owned();

            cache.layer_caches[layer_idx] = (present_k, present_v);
        }

        // Return logits for the single token (shape: 1, vocab_size)
        let result = logits
            .slice(ndarray::s![0, 0, ..])
            .to_owned()
            .to_shape((1, self.vocab_size))?
            .to_owned();

        Ok(result)
    }
}

/// Cache for KV states during generation
#[derive(Clone)]
pub struct GenerationCache {
    /// For each layer: (key, value) tensors
    /// Shape: (1, n_heads, seq_len, head_dim)
    pub(crate) layer_caches: Vec<(Array4<f32>, Array4<f32>)>,
}

impl GenerationCache {
    /// Create a new empty cache
    pub fn new(n_layers: usize, n_heads: usize, head_dim: usize) -> Self {
        // Create empty caches with shape (1, n_heads, 0, head_dim)
        let empty_cache = (1, n_heads, 0, head_dim);
        Self {
            layer_caches: vec![(Array4::zeros(empty_cache), Array4::zeros(empty_cache)); n_layers],
        }
    }

    fn empty(n_layers: usize, n_heads: usize, head_dim: usize) -> Self {
        Self::new(n_layers, n_heads, head_dim)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_generative_model_placeholder() {
        // This is a placeholder test. Actual tests will depend on having a model file.
        // For now, we just ensure the module compiles.
        assert!(true);
    }
}
