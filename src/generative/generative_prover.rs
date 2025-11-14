use std::borrow::Cow;
use std::error::Error;
use std::time::Instant;

use crate::binding_map::BindingMap;
use crate::certificate::Certificate;
use crate::checker::Checker;
use crate::code_generator::Error as CodeGenError;
use crate::goal::Goal;
use crate::normalizer::{NormalizedGoal, Normalizer};
use crate::project::Project;
use crate::proof_step::ProofStep;
use crate::prover::{Outcome, Prover, ProverMode};

use super::generative_model::{GenerationCache, GenerativeModel};
use super::goal_context::GoalContext;

/// Configuration for the generative prover
#[derive(Clone, Debug)]
pub struct GenerativeProverConfig {
    /// Path to the directory containing model.onnx, tokenizer.json, config.json
    pub generative_model_path: String,

    /// Number of generation steps to attempt per rollout
    pub num_steps_per_rollout: usize,

    /// Maximum tokens to generate per line
    pub max_tokens_per_line: usize,

    /// Sampling temperature for generation (higher = more random)
    pub temperature: f32,

    /// Time limit in seconds for a rollout (default: 5.0)
    pub time_limit_secs: f32,
}

impl Default for GenerativeProverConfig {
    fn default() -> Self {
        Self {
            generative_model_path: String::new(),
            num_steps_per_rollout: 10,
            max_tokens_per_line: 100,
            temperature: 0.8,
            time_limit_secs: 5.0,
        }
    }
}

/// A generative theorem prover that uses a neural language model to generate proof steps
#[derive(Clone)]
pub struct GenerativeProver {
    /// The neural model for generating proof tactics
    generative_model: GenerativeModel,

    /// Configuration parameters
    config: GenerativeProverConfig,

    /// Context for the current goal (if set)
    goal_context: Option<GoalContext>,

    /// Cache for the goal context and successfully checked lines
    /// This grows as we add successful lines to the context
    context_cache: Option<GenerationCache>,

    /// Initial state: the base cache with just the goal context (before any generated lines)
    /// This is cloned at the start of each rollout
    initial_cache: Option<GenerationCache>,

    /// Statistics about the current rollout
    successful_lines: usize,
    failed_attempts: usize,

    /// Overall statistics across all rollouts
    total_successful_lines: usize,
    total_failed_attempts: usize,

    /// The goal name (used for certificate generation)
    goal_name: Option<String>,

    /// The certificate found during search (if a successful proof was found)
    certificate: Option<Certificate>,
}

impl GenerativeProver {
    /// Create a new GenerativeProver from a config
    pub fn new(config: GenerativeProverConfig) -> Self {
        let generative_model = GenerativeModel::load(&config.generative_model_path)
            .expect("Failed to load generative model");

        Self {
            generative_model,
            config,
            goal_context: None,
            context_cache: None,
            initial_cache: None,
            successful_lines: 0,
            failed_attempts: 0,
            total_successful_lines: 0,
            total_failed_attempts: 0,
            goal_name: None,
            certificate: None,
        }
    }

    /// Set the goal context and initialize the KV cache with the prompt
    /// This should be called once before starting generation
    pub fn set_goal_context(&mut self, goal_context: GoalContext) -> Result<(), Box<dyn Error>> {
        // Build the prompt from the goal context
        let mut prompt = Vec::new();
        goal_context.write_to(&mut prompt)?;
        let prompt = String::from_utf8(prompt)?;

        // Tokenize the prompt
        let tokens = self.generative_model.encode(&prompt);

        // Initialize a cache and warm it up with the prompt tokens
        let mut cache = GenerationCache::new(
            self.generative_model.n_layers(),
            self.generative_model.n_heads(),
            self.generative_model.head_dim(),
        );

        // Run inference on each token to populate the cache
        for &token in &tokens {
            self.generative_model.infer_with_cache(token, &mut cache)?;
        }

        self.goal_context = Some(goal_context);
        // Store both as initial state (for rollout resets) and current state
        self.initial_cache = Some(cache.clone());
        self.context_cache = Some(cache);

        Ok(())
    }

    /// Reset state for a new rollout
    /// This restores the cache to its initial state (just the goal context)
    fn reset_for_new_rollout(&mut self) {
        // Accumulate rollout stats into overall stats
        self.total_successful_lines += self.successful_lines;
        self.total_failed_attempts += self.failed_attempts;

        // Clone the initial cache (with just goal context, no generated lines)
        if let Some(ref initial_cache) = self.initial_cache {
            self.context_cache = Some(initial_cache.clone());
        }

        // Reset per-rollout statistics
        self.successful_lines = 0;
        self.failed_attempts = 0;
    }

    /// Attempt to generate and check a single line
    /// Returns Some(line) if the line checked successfully, None if it failed to check
    ///
    /// On success: the cache is updated with the new line, so future generations build on it
    /// On failure: the cache is unchanged, so the failed line doesn't pollute context
    pub fn generate_and_check_line(
        &mut self,
        checker: &mut Checker,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Cow<Normalizer>,
    ) -> Option<String> {
        // Get the cache (must be initialized via set_goal_context)
        let base_cache = self
            .context_cache
            .as_ref()
            .expect("No goal context set - call set_goal_context first");

        // Clone the cache before generation
        // If the line fails to check, we discard this clone
        // If it succeeds, we keep it (with the new line tokens added)
        let mut working_cache = base_cache.clone();

        // Generate a line using the cloned cache
        let generated_line = self
            .generative_model
            .generate_line_with_cache(
                &mut working_cache,
                self.config.max_tokens_per_line,
                self.config.temperature,
            )
            .expect("Failed to generate line");

        // Try to check the generated line
        let mut certificate_steps = Vec::new();

        match checker.check_code(
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
                Some(generated_line)
            }
            Err(_) => {
                // Failed to check - checker state unchanged
                // Discard the working_cache, keep the original
                self.failed_attempts += 1;
                None
            }
        }
    }

    /// Run a single rollout: generate up to num_steps_per_rollout lines
    /// Stops early if we find a contradiction
    /// Returns Some(accepted_lines) if a contradiction was found, None otherwise
    pub fn rollout(
        &mut self,
        checker: &mut Checker,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Cow<Normalizer>,
    ) -> Option<Vec<String>> {
        let mut accepted_lines = Vec::new();

        for _ in 0..self.config.num_steps_per_rollout {
            // Check if we've already found a contradiction
            if checker.has_contradiction() {
                return Some(accepted_lines);
            }

            // Try to generate and check a line
            // Returns Some(line) if successful, None if failed to check
            if let Some(line) = self.generate_and_check_line(checker, project, bindings, normalizer)
            {
                accepted_lines.push(line);
            }
        }

        // Exhausted our step budget for this rollout
        if checker.has_contradiction() {
            Some(accepted_lines)
        } else {
            None
        }
    }

    /// Run a full search: perform multiple rollouts until time runs out or proof is found
    pub fn search(
        &mut self,
        project: &Project,
        bindings: &BindingMap,
        normalizer: &Normalizer,
        checker: &Checker,
    ) -> Outcome {
        let start_time = Instant::now();
        let time_limit = std::time::Duration::from_secs_f32(self.config.time_limit_secs);

        // Wrap in Cow for internal methods
        let mut bindings = Cow::Borrowed(bindings);
        let mut normalizer = Cow::Borrowed(normalizer);

        loop {
            // Check if we've hit the time limit
            if start_time.elapsed() >= time_limit {
                break;
            }

            // Clone the checker for this rollout
            let mut rollout_checker = checker.clone();

            // Run a single rollout
            if let Some(accepted_lines) = self.rollout(
                &mut rollout_checker,
                project,
                &mut bindings,
                &mut normalizer,
            ) {
                // Success! We found a contradiction
                // Create and save the certificate
                if let Some(ref goal_name) = self.goal_name {
                    self.certificate = Some(Certificate::new(goal_name.clone(), accepted_lines));
                }
                return Outcome::Success;
            }

            // Rollout didn't find a contradiction, continue trying
            self.reset_for_new_rollout();
            continue;
        }

        // Time limit exhausted
        Outcome::Timeout
    }

    /// Get statistics about the overall search (across all rollouts)
    pub fn stats(&self) -> (usize, usize) {
        // Include current rollout stats if any
        (
            self.total_successful_lines + self.successful_lines,
            self.total_failed_attempts + self.failed_attempts,
        )
    }
}

impl Prover for GenerativeProver {
    fn box_clone(&self) -> Box<dyn Prover> {
        Box::new(self.clone())
    }

    /// Add proof steps to the prover
    /// For the generative prover, we don't use explicit proof steps - the model generates them
    fn add_steps(&mut self, _steps: Vec<ProofStep>) {
        // The generative prover doesn't use explicit proof steps
        // It gets them indirectly through the Checker
    }

    /// Set the goal and initialize the prover
    fn set_goal(
        &mut self,
        _goal: NormalizedGoal,
        _steps: Vec<ProofStep>,
        project: &Project,
        original_goal: &Goal,
    ) {
        // Save the goal name for certificate generation
        self.goal_name = Some(original_goal.name.clone());

        // Create a goal context from the original goal
        let goal_context = GoalContext::from_project_and_goal(project, original_goal)
            .expect("Failed to create goal context from goal");

        // Set the goal context
        self.set_goal_context(goal_context)
            .expect("Failed to set goal context");
    }

    /// Run the proof search
    fn search(
        &mut self,
        _mode: ProverMode,
        project: &Project,
        bindings: &BindingMap,
        normalizer: &Normalizer,
        checker: &Checker,
    ) -> Outcome {
        self.search(project, bindings, normalizer, checker)
    }

    /// Generate a certificate for the proof
    /// Returns the certificate if a successful proof was found, otherwise returns an error
    fn make_cert(
        &self,
        _project: &Project,
        _bindings: &BindingMap,
        _normalizer: &Normalizer,
        print: bool,
    ) -> Result<Certificate, CodeGenError> {
        let cert = self
            .certificate
            .as_ref()
            .ok_or_else(|| CodeGenError::GeneratedBadCode("No proof found".to_string()))?;

        if print {
            println!("concrete proof:");
            if let Some(proof) = &cert.proof {
                for line in proof {
                    println!("  {}", line);
                }
            } else {
                println!("  <no proof>");
            }
        }
        Ok(cert.clone())
    }
}
