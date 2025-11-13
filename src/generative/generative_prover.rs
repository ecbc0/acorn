use std::borrow::Cow;
use std::error::Error;

use crate::binding_map::BindingMap;
use crate::checker::Checker;
use crate::normalizer::Normalizer;
use crate::project::Project;

use super::goal_context::GoalContext;
use super::tactics_model::{GenerationCache, TacticsModel};

/// Configuration for the generative prover
#[derive(Clone, Debug)]
pub struct GenerativeProverConfig {
    /// Path to the directory containing model.onnx, tokenizer.json, config.json
    pub tactics_model_path: String,

    /// Number of generation steps to attempt per rollout
    pub num_steps_per_rollout: usize,

    /// Maximum tokens to generate per line
    pub max_tokens_per_line: usize,

    /// Sampling temperature for generation (higher = more random)
    pub temperature: f32,
}

impl Default for GenerativeProverConfig {
    fn default() -> Self {
        Self {
            tactics_model_path: String::new(),
            num_steps_per_rollout: 10,
            max_tokens_per_line: 100,
            temperature: 0.8,
        }
    }
}

/// Result of a rollout attempt
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RolloutOutcome {
    /// Found a contradiction (proof complete!)
    Proved,

    /// Exhausted num_steps_per_rollout without finding contradiction
    Incomplete,

    /// Hit an error during generation or checking
    Error(String),
}

/// A generative theorem prover that uses a neural language model to generate proof steps
pub struct GenerativeProver {
    /// The neural model for generating proof tactics
    tactics_model: TacticsModel,

    /// The checker for verifying generated steps
    checker: Checker,

    /// Configuration parameters
    config: GenerativeProverConfig,

    /// Context for the current goal (if set)
    goal_context: Option<GoalContext>,

    /// Cache for the goal context and successfully checked lines
    /// This grows as we add successful lines to the context
    context_cache: Option<GenerationCache>,

    /// Statistics about the current rollout
    successful_lines: usize,
    failed_attempts: usize,
}

impl GenerativeProver {
    /// Create a new GenerativeProver from a config and initial checker state
    pub fn new(config: GenerativeProverConfig, checker: Checker) -> Result<Self, Box<dyn Error>> {
        let tactics_model = TacticsModel::load(&config.tactics_model_path)?;

        Ok(Self {
            tactics_model,
            checker,
            config,
            goal_context: None,
            context_cache: None,
            successful_lines: 0,
            failed_attempts: 0,
        })
    }

    /// Set the goal context and initialize the KV cache with the prompt
    /// This should be called once before starting generation
    pub fn set_goal_context(&mut self, goal_context: GoalContext) -> Result<(), Box<dyn Error>> {
        // Build the prompt from the goal context
        let mut prompt = Vec::new();
        goal_context.write_to(&mut prompt)?;
        let prompt = String::from_utf8(prompt)?;

        // Tokenize the prompt
        let tokens = self.tactics_model.encode(&prompt);

        // Initialize a cache and warm it up with the prompt tokens
        let mut cache = GenerationCache::new(
            self.tactics_model.n_layers(),
            self.tactics_model.n_heads(),
            self.tactics_model.head_dim(),
        );

        // Run inference on each token to populate the cache
        for &token in &tokens {
            self.tactics_model.infer_with_cache(token, &mut cache)?;
        }

        self.goal_context = Some(goal_context);
        self.context_cache = Some(cache);

        Ok(())
    }

    /// Attempt to generate and check a single line
    /// Returns Ok(true) if the line checked successfully, Ok(false) if it failed to check
    ///
    /// On success: the cache is updated with the new line, so future generations build on it
    /// On failure: the cache is unchanged, so the failed line doesn't pollute context
    pub fn generate_and_check_line(
        &mut self,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Cow<Normalizer>,
    ) -> Result<bool, Box<dyn Error>> {
        // Make sure we have a cache initialized
        let base_cache = self
            .context_cache
            .as_ref()
            .ok_or("No goal context set - call set_goal_context first")?;

        // Clone the cache before generation
        // If the line fails to check, we discard this clone
        // If it succeeds, we keep it (with the new line tokens added)
        let mut working_cache = base_cache.clone();

        // Generate a line using the cloned cache
        let generated_line = self.tactics_model.generate_line_with_cache(
            &mut working_cache,
            self.config.max_tokens_per_line,
            self.config.temperature,
        )?;

        // Try to check the generated line
        let mut certificate_steps = Vec::new();

        match self.checker.check_code(
            &generated_line,
            project,
            bindings,
            normalizer,
            &mut certificate_steps,
        ) {
            Ok(()) => {
                // Success! The checker has been updated
                // Keep the updated cache (which now includes the generated line tokens)
                self.context_cache = Some(working_cache);
                self.successful_lines += 1;
                Ok(true)
            }
            Err(_) => {
                // Failed to check - checker state unchanged
                // Discard the working_cache, keep the original
                self.failed_attempts += 1;
                Ok(false)
            }
        }
    }

    /// Run a full rollout: generate up to num_steps_per_rollout lines
    /// Stops early if we find a contradiction
    pub fn rollout(
        &mut self,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Cow<Normalizer>,
    ) -> RolloutOutcome {
        for _ in 0..self.config.num_steps_per_rollout {
            // Check if we've already found a contradiction
            if self.has_contradiction() {
                return RolloutOutcome::Proved;
            }

            // Try to generate and check a line
            match self.generate_and_check_line(project, bindings, normalizer) {
                Ok(true) => {
                    // Successfully checked a line, continue
                }
                Ok(false) => {
                    // Failed to check, but that's okay - just try again
                }
                Err(e) => {
                    return RolloutOutcome::Error(e.to_string());
                }
            }
        }

        // Exhausted our step budget
        if self.has_contradiction() {
            RolloutOutcome::Proved
        } else {
            RolloutOutcome::Incomplete
        }
    }

    /// Check if we've found a contradiction (proof complete)
    pub fn has_contradiction(&self) -> bool {
        self.checker.has_contradiction()
    }

    /// Get statistics about the current search
    pub fn stats(&self) -> (usize, usize) {
        (self.successful_lines, self.failed_attempts)
    }
}
