use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::atomic::AtomicU32;
use std::time::Duration;

use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Range};

use crate::block::NodeCursor;
use crate::build_cache::BuildCache;
use crate::certificate::{Certificate, CertificateStore, CertificateWorklist};
use crate::compilation::CompilationError;
use crate::environment::Environment;
use crate::goal::Goal;
use crate::module::{LoadState, ModuleDescriptor, ModuleId};
use crate::module_cache::ModuleCache;
use crate::processor::Processor;
use crate::project::Project;
use crate::prover::{Outcome, ProverParams};

static NEXT_BUILD_ID: AtomicU32 = AtomicU32::new(1);

/// The Builder contains all the mutable state for a single build.
/// This is separate from the Project because you can read information from the Project from other
/// threads while a build is ongoing, but a Builder is only used by the build itself.
pub struct Builder<'a> {
    /// Reference to the project being built.
    project: &'a Project,

    /// A single event handler is used across all modules.
    event_handler: Box<dyn FnMut(BuildEvent) + 'a>,

    pub status: BuildStatus,

    /// A unique id for each build.
    pub id: u32,

    /// Build metrics collected during verification.
    pub metrics: BuildMetrics,

    /// When this flag is set, we emit build events when a goal is slow.
    pub log_when_slow: bool,

    /// When this flag is set, we emit build events for secondary errors.
    /// I.e., errors that happen when you try to import a module that itself has an error.
    pub log_secondary_errors: bool,

    /// In reverify mode, we are checking to make sure that all goals are covered by existing certs.
    /// In this situation, it's an error if we run into any goal that is missing a cert,
    /// or any cert that fails checking.
    /// In normal mode, this is okay, because it could be that we modified the file.
    pub reverify: bool,

    /// Whether we skip goals that match hashes in the cache.
    pub check_hashes: bool,

    /// The current module we are proving.
    current_module: Option<ModuleDescriptor>,

    /// Whether the current module has neither errors nor warnings.
    /// I guess if there is no current module, it's vacuously good.
    current_module_good: bool,

    /// The new build cache, that is being produced as a result of this build.
    pub build_cache: Option<BuildCache>,

    /// When this is set, the builder only builds a single goal.
    /// We specify goal by (module, line number).
    /// This is an internal line number, which starts at 0.
    pub single_goal: Option<(ModuleDescriptor, u32)>,

    /// The verbose flag makes us print miscellaneous debug output.
    /// Don't set it from within the language server.
    pub verbose: bool,

    /// Cancellation token to stop the build.
    cancellation_token: CancellationToken,
}

/// Metrics collected during a build.
#[derive(Clone, Debug, Default)]
pub struct BuildMetrics {
    /// The total number of modules to be built.
    pub modules_total: i32,

    /// The number of modules we skipped due to caching.
    pub modules_cached: i32,

    /// The total number of goals to be verified.
    pub goals_total: i32,

    /// The number of goals that we have processed in the build.
    pub goals_done: i32,

    /// The number of goals that were successfully proven.
    pub goals_success: i32,

    /// How many certificates were reused from the cache.
    pub certs_cached: i32,

    /// How many cached certificates were unused.
    pub certs_unused: i32,

    /// How many new certificates were created in this build.
    pub certs_created: i32,

    /// How many proof searches we did.
    pub searches_total: i32,

    /// Number of proof searches that ended in success.
    pub searches_success: i32,

    /// The number of searches that we ran the full prover on.
    pub searches_full: i32,

    /// The number of searches that we ran the filtered prover on.
    pub searches_filtered: i32,

    /// The number of searches where we had to do a fallback.
    pub searches_fallback: i32,

    /// The total number of clauses activated.
    pub clauses_activated: i32,

    /// Total sum of square num_activated.
    pub clauses_sum_square_activated: u64,

    /// Total number of clauses scored, both active and passive.
    pub clauses_total: i32,

    /// The total amount of time spent in proof search, in seconds.
    pub search_time: f64,
}

#[derive(Debug)]
pub struct BuildError {
    pub range: Range,
    pub message: String,
}

impl BuildError {
    pub fn new(range: Range, message: impl Into<String>) -> Self {
        BuildError {
            range,
            message: message.into(),
        }
    }

    /// A build error that occurred at a particular goal.
    fn goal(goal: &Goal, message: impl Into<String>) -> Self {
        let message = format!("{} {}", goal.name, message.into());
        BuildError {
            range: goal.proposition.source.range,
            message,
        }
    }
}

impl From<BuildError> for String {
    fn from(error: BuildError) -> String {
        error.message
    }
}

impl BuildMetrics {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn print(&self, status: BuildStatus) {
        println!();
        if self.modules_cached > 0 {
            println!(
                "{}/{} modules cached",
                self.modules_cached, self.modules_total
            );
        }
        if self.certs_created > 0 {
            println!("{} certificates created", self.certs_created);
        }
        if self.certs_cached > 0 {
            println!("{} certificates cached", self.certs_cached);
        }
        if self.certs_unused > 0 {
            println!("{} certificates unused", self.certs_unused);
        }
        println!(
            "{} searches performed ({} full, {} filtered, {} fallback)",
            self.searches_total, self.searches_full, self.searches_filtered, self.searches_fallback
        );
        if self.searches_total > 0 {
            let success_percent = 100.0 * self.searches_success as f64 / self.searches_total as f64;
            println!("{:.2}% search success rate", success_percent);
            let num_activated = self.clauses_activated as f64 / self.searches_success as f64;
            println!("{:.2} average activations", num_activated);
            let mean_square_activated =
                self.clauses_sum_square_activated as f64 / self.searches_total as f64;
            println!("{:.1} mean square activations", mean_square_activated);
            let num_clauses = self.clauses_total as f64 / self.searches_total as f64;
            println!("{:.2} average clauses", num_clauses);
            let search_time_ms = 1000.0 * self.search_time / self.searches_total as f64;
            println!("{:.1} ms average search time", search_time_ms);
        }
        println!("{}/{} OK", self.goals_success, self.goals_total);
        match status {
            BuildStatus::Error => {
                println!("Compilation failed.");
            }
            BuildStatus::Warning => {
                println!("Verification failed.");
            }
            BuildStatus::Good => {
                println!("Verification succeeded.");
            }
        }
    }
}

/// A "build" is when we verify a set of goals, determined by a Project.
/// For each build, we report many  build events.
#[derive(Debug, Clone)]
pub struct BuildEvent {
    /// Which build this is an event for.
    pub build_id: u32,

    /// Current progress is done / total.
    /// This is across all modules.
    pub progress: Option<(i32, i32)>,

    /// Human-readable
    pub log_message: Option<String>,

    /// The module that the build event is coming from.
    pub module: ModuleDescriptor,

    /// Whenever we run into a problem, report a diagnostic.
    pub diagnostic: Option<Diagnostic>,

    /// Whenever we verify a goal, report the lines that the goal covers.
    /// Note that this is only the final goal. Subgoals might have failed to verify.
    pub verified: Option<(u32, u32)>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BuildStatus {
    /// No problems of any kind
    Good,

    /// Warnings indicate code that parses okay but can't be verified
    Warning,

    /// Errors indicate either the user entered bad code, or we ran into a bug in the build process
    Error,
}

impl BuildStatus {
    pub fn verb(&self) -> &str {
        match self {
            BuildStatus::Good => "succeeded",
            BuildStatus::Warning => "warned",
            BuildStatus::Error => "errored",
        }
    }

    pub fn warn(&mut self) {
        if *self == BuildStatus::Good {
            *self = BuildStatus::Warning;
        }
    }

    pub fn is_error(&self) -> bool {
        match self {
            BuildStatus::Error => true,
            _ => false,
        }
    }

    pub fn is_good(&self) -> bool {
        match self {
            BuildStatus::Good => true,
            _ => false,
        }
    }
}

impl<'a> Builder<'a> {
    pub fn new(
        project: &'a Project,
        cancellation_token: CancellationToken,
        event_handler: impl FnMut(BuildEvent) + 'a,
    ) -> Self {
        let event_handler = Box::new(event_handler);
        Builder {
            project,
            event_handler,
            status: BuildStatus::Good,
            id: NEXT_BUILD_ID.fetch_add(1, std::sync::atomic::Ordering::SeqCst),
            metrics: BuildMetrics::new(),
            log_when_slow: false,
            log_secondary_errors: true,
            reverify: false,
            check_hashes: true,
            current_module: None,
            current_module_good: true,
            build_cache: None,
            single_goal: None,
            verbose: false,
            cancellation_token,
        }
    }

    fn default_event(&self) -> BuildEvent {
        BuildEvent {
            build_id: self.id,
            progress: None,
            log_message: None,
            module: self.module().clone(),
            diagnostic: None,
            verified: None,
        }
    }

    /// Returns Anonymous while loading
    fn module(&self) -> ModuleDescriptor {
        match &self.current_module {
            None => ModuleDescriptor::Anonymous,
            Some(m) => m.clone(),
        }
    }

    /// Called when a single module is loaded successfully.
    pub fn module_loaded(&mut self, env: &Environment) {
        self.metrics.goals_total += env.iter_goals().count() as i32;
    }

    /// Called when the entire loading phase is done.
    pub fn loading_phase_complete(&mut self) {
        let event = BuildEvent {
            progress: Some((0, self.metrics.goals_total)),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    /// Logs an informational message not tied to any particular location.
    /// In VS Code this will only appear in a pane, so it's only useful for debugging.
    /// You can't expect a typical user to see these.
    /// This doesn't change build status.
    pub fn log_global(&mut self, message: String) {
        let event = BuildEvent {
            log_message: Some(message),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    /// Logs an error during the loading phase, that can be localized to a particular place.
    pub fn log_loading_error(&mut self, descriptor: &ModuleDescriptor, error: &CompilationError) {
        let diagnostic = Diagnostic {
            range: error.range(),
            severity: Some(DiagnosticSeverity::ERROR),
            message: error.to_string(),
            ..Diagnostic::default()
        };
        let event = BuildEvent {
            log_message: Some(format!("compilation error: {}", error)),
            module: descriptor.clone(),
            diagnostic: Some(diagnostic),
            ..self.default_event()
        };
        (self.event_handler)(event);
        self.status = BuildStatus::Error;
    }

    /// Called when we start proving a module.
    pub fn module_proving_started(&mut self, descriptor: ModuleDescriptor) {
        self.current_module = Some(descriptor);
        self.current_module_good = true;
    }

    /// Returns whether the module completed without any errors or warnings.
    pub fn module_proving_complete(&mut self, module: &ModuleDescriptor) -> bool {
        assert_eq!(&self.module(), module);
        let answer = self.current_module_good;
        self.current_module = None;
        self.current_module_good = true;
        answer
    }

    /// Called when a single proof search completes.
    /// Statistics are tracked here.
    /// env should be the environment that the proof happened in.
    pub fn search_finished(
        &mut self,
        processor: &Processor,
        goal: &Goal,
        outcome: Outcome,
        elapsed: Duration,
    ) {
        // Time conversion
        let secs = elapsed.as_secs() as f64;
        let subsec_nanos = elapsed.subsec_nanos() as f64;
        let elapsed_f64 = secs + subsec_nanos * 1e-9;
        let elapsed_str = format!("{:.3}s", elapsed_f64);

        // Tracking statistics
        self.metrics.goals_done += 1;
        self.metrics.searches_total += 1;
        self.metrics.search_time += elapsed_f64;
        let clauses_activated = processor.prover().num_activated() as i32;
        self.metrics.clauses_activated += clauses_activated;
        let num_passive = processor.prover().num_passive() as i32;
        self.metrics.clauses_total += clauses_activated + num_passive;
        self.metrics.clauses_sum_square_activated += (clauses_activated * clauses_activated) as u64;

        match outcome {
            Outcome::Success => {
                // The search was a success.
                self.metrics.goals_success += 1;
                self.metrics.searches_success += 1;
                if self.log_when_slow && elapsed_f64 > 0.1 {
                    self.log_info(&goal, &format!("took {}", elapsed_str));
                }
                self.log_verified(goal.first_line, goal.last_line);
            }
            Outcome::Exhausted => self.log_warning(&goal, "could not be verified (exhaustion)"),
            Outcome::Inconsistent => self.log_warning(&goal, "- prover found an inconsistency"),
            Outcome::Timeout => self.log_warning(
                &goal,
                &format!("could not be verified (timeout after {})", elapsed_str),
            ),
            Outcome::Interrupted => {
                // Should this really be an error?
                let error = BuildError::goal(&goal, "was interrupted");
                self.log_build_error(&error);
            }
            Outcome::Constrained => self.log_warning(&goal, "could not be verified (constraints)"),
        }
    }

    /// Logs a successful verification.
    /// This can either be a proof, or something that doesn't require proving.
    pub fn log_verified(&mut self, first_line: u32, last_line: u32) {
        let event = BuildEvent {
            progress: Some((self.metrics.goals_done, self.metrics.goals_total)),
            verified: Some((first_line, last_line)),
            ..self.default_event()
        };
        (self.event_handler)(event);
    }

    /// Logs a cache hit for this node and every child of it.
    /// Returns the cursor to its initial state when done.
    pub fn log_proving_cache_hit(&mut self, cursor: &mut NodeCursor) {
        if cursor.num_children() > 0 {
            cursor.descend(0);
            loop {
                self.log_proving_cache_hit(cursor);
                if cursor.has_next() {
                    cursor.next();
                } else {
                    break;
                }
            }
            cursor.ascend();
        }
        if cursor.node().has_goal() {
            let goal = cursor.goal().unwrap();
            self.metrics.goals_done += 1;
            self.metrics.goals_success += 1;
            self.log_verified(goal.first_line, goal.last_line);
        }
    }

    /// Create a build event for a proof that was other than successful.
    fn make_event(&mut self, range: Range, message: &str, sev: DiagnosticSeverity) -> BuildEvent {
        let diagnostic = Diagnostic {
            range,
            severity: Some(sev),
            message: message.to_string(),
            ..Diagnostic::default()
        };
        BuildEvent {
            progress: Some((self.metrics.goals_done, self.metrics.goals_total)),
            log_message: Some(message.to_string()),
            diagnostic: Some(diagnostic),
            ..self.default_event()
        }
    }

    /// Note that this will blue-squiggle in VS Code, so don't just use this willy-nilly.
    fn log_info(&mut self, goal: &Goal, message: &str) {
        let full_message = format!("{} {}", goal.name, message);
        let event = self.make_event(
            goal.proposition.source.range,
            &full_message,
            DiagnosticSeverity::INFORMATION,
        );
        (self.event_handler)(event);
    }

    /// Logs a warning that is associated with a particular goal.
    /// This will cause a yellow squiggle in VS Code.
    /// This will mark the build as "not good", so we won't cache it.
    fn log_warning(&mut self, goal: &Goal, message: &str) {
        let full_message = format!("{} {}", goal.name, message);
        let event = self.make_event(
            goal.proposition.source.range,
            &full_message,
            DiagnosticSeverity::WARNING,
        );
        (self.event_handler)(event);
        self.current_module_good = false;
        self.status.warn();
    }

    /// Logs an error that is associated with a particular goal.
    /// This will cause a red squiggle in VS Code.
    /// This will halt the build.
    fn log_build_error(&mut self, build_error: &BuildError) {
        let mut event = self.make_event(
            build_error.range,
            &build_error.message,
            DiagnosticSeverity::ERROR,
        );

        // Set progress as complete, because an error will halt the build
        event.progress = Some((self.metrics.goals_total, self.metrics.goals_total));
        (self.event_handler)(event);
        self.current_module_good = false;
        self.status = BuildStatus::Error;
    }

    /// Sets the builder to only build a single goal.
    /// Takes a target module name and an external line number (1-based).
    /// Does not check that there is a goal at this line.
    /// Requires that the target module is already loaded.
    pub fn set_single_goal(
        &mut self,
        target: &str,
        external_line_number: u32,
    ) -> Result<(), String> {
        // Convert from 1-based (external) to 0-based (internal) line number
        let internal_line_number = external_line_number - 1;

        let module_id = self
            .project
            .get_module_id_by_name(target)
            .ok_or_else(|| format!("Module '{}' not found", target))?;

        let module_descriptor = self
            .project
            .get_module_descriptor(module_id)
            .ok_or_else(|| format!("No descriptor found for module '{}'", target))?
            .clone();

        self.single_goal = Some((module_descriptor, internal_line_number));
        Ok(())
    }

    /// Returns None if we don't have cached premises for this block.
    /// cursor points to the node we are verifying.
    pub fn make_filtered_processor(
        &self,
        env: &Environment,
        block_name: &str,
        module_cache: &Option<ModuleCache>,
    ) -> Result<Option<Rc<Processor>>, BuildError> {
        // Load the premises from the cache
        let Some(normalized) = module_cache
            .as_ref()
            .and_then(|mc| mc.blocks.get(block_name))
        else {
            return Ok(None);
        };

        let mut premises = HashMap::new();
        for (module_name, premise_set) in normalized.iter() {
            // A module could have been renamed, in which case the whole cache is borked.
            let Some(module_id) = self.project.get_module_id_by_name(module_name) else {
                return Ok(None);
            };
            premises.insert(module_id, premise_set.iter().cloned().collect());
        }
        let mut processor = Processor::with_token(self.cancellation_token.clone());

        // Add facts from the dependencies
        let empty = HashSet::new();
        for module_id in self.project.all_dependencies(env.module_id) {
            let module_premises = match premises.get(&module_id) {
                Some(p) => p,
                None => &empty,
            };
            let module_env = self.project.get_env_by_id(module_id).unwrap();
            // importable_facts will always include extends and instance facts,
            // even when a filter is provided
            for fact in module_env.importable_facts(Some(module_premises)) {
                processor.add_fact(fact)?;
            }
        }

        // Find the index of the block with the given name
        let Some(block_index) = env.get_block_index(block_name) else {
            return Ok(None);
        };

        // Add facts from this file itself, but only up to the block we're proving
        let local_premises = premises.get(&env.module_id);
        for node in env.nodes.iter().take(block_index) {
            let Some(fact) = node.get_fact() else {
                continue;
            };

            // Always include facts that are used in normalization.
            if fact.used_in_normalization() {
                processor.add_fact(fact)?;
                continue;
            }

            let Some(name) = node.source_name() else {
                continue;
            };
            let Some(local_premises) = local_premises else {
                continue;
            };

            if local_premises.contains(&name) {
                processor.add_fact(fact)?;
            }
        }

        Ok(Some(Rc::new(processor)))
    }

    /// Verifies a goal with fallback from filtered to full prover.
    /// env should be the environment that the proof happens in.
    fn verify_with_fallback(
        &mut self,
        mut full_processor: Rc<Processor>,
        filtered_processor: Option<Rc<Processor>>,
        goal: &Goal,
        env: &Environment,
        mut new_certs: Option<&mut Vec<Certificate>>,
        mut worklist: Option<&mut CertificateWorklist>,
        new_premises: &mut HashSet<(ModuleId, String)>,
    ) -> Result<(), BuildError> {
        // Check if we've been cancelled before starting any work
        if self.cancellation_token.is_cancelled() {
            return Err(BuildError::goal(goal, "was interrupted"));
        }

        // Check for a cached cert
        if let Some(worklist) = worklist.as_mut() {
            let indexes = worklist.get_indexes(&goal.name);
            for i in indexes {
                let cert = worklist.get_cert(*i).unwrap();
                match full_processor.check_cert(cert, Some(goal), self.project, &env.bindings) {
                    Ok(()) => {
                        self.metrics.certs_cached += 1;
                        self.metrics.goals_done += 1;
                        self.metrics.goals_success += 1;
                        self.log_verified(goal.first_line, goal.last_line);
                        if let Some(new_certs) = new_certs.as_mut() {
                            new_certs.push(cert.clone());
                        }
                        worklist.remove(&goal.name, *i);
                        return Ok(());
                    }
                    Err(e) if self.reverify => {
                        // In reverify mode, a bad cert is an error
                        return Err(BuildError::goal(
                            goal,
                            &format!("certificate failed to verify: {}", e),
                        ));
                    }
                    Err(_) => {
                        // The cert is bad, but maybe another one is good.
                        // That can happen with code edits.
                    }
                }
            }
        } else if self.reverify {
            return Err(BuildError::goal(goal, "no worklist found"));
        }

        // In reverify mode, we should never reach the search phase
        if self.reverify {
            return Err(BuildError::goal(goal, "no certificate found"));
        }

        // Try the filtered prover
        if let Some(mut filtered_processor) = filtered_processor {
            self.metrics.searches_filtered += 1;
            let filtered_processor = Rc::make_mut(&mut filtered_processor);
            filtered_processor.set_goal(goal)?;
            let start = std::time::Instant::now();
            let outcome = filtered_processor.search(ProverParams::VERIFICATION);
            if outcome == Outcome::Success {
                if let Some(new_certs) = new_certs.as_mut() {
                    match filtered_processor.make_cert(self.project, &env.bindings, self.verbose) {
                        Ok(cert) => {
                            new_certs.push(cert);
                            self.metrics.certs_created += 1;
                        }
                        Err(e) => {
                            return Err(BuildError::goal(
                                &goal,
                                &format!("filtered prover failed to create certificate: {}", e),
                            ));
                        }
                    }
                }
                self.search_finished(filtered_processor, goal, outcome, start.elapsed());
                filtered_processor
                    .prover()
                    .get_useful_source_names(new_premises, filtered_processor.normalizer());
                return Ok(());
            }
            self.metrics.searches_fallback += 1;
        }

        // Try the full prover
        let full_processor = Rc::make_mut(&mut full_processor);
        full_processor.set_goal(goal)?;
        self.metrics.searches_full += 1;
        let start = std::time::Instant::now();
        let outcome = full_processor.search(ProverParams::VERIFICATION);
        if outcome == Outcome::Success {
            if let Some(new_certs) = new_certs.as_mut() {
                match full_processor.make_cert(self.project, &env.bindings, self.verbose) {
                    Ok(cert) => {
                        new_certs.push(cert);
                        self.metrics.certs_created += 1;
                    }
                    Err(e) => {
                        return Err(BuildError::goal(
                            &goal,
                            &format!("full prover failed to create certificate: {}", e),
                        ));
                    }
                }
            }
        }
        self.search_finished(full_processor, goal, outcome, start.elapsed());
        full_processor
            .prover()
            .get_useful_source_names(new_premises, full_processor.normalizer());
        Ok(())
    }

    /// Verifies a node and all its children recursively.
    /// builder tracks statistics and results for the build.
    /// If verify_node encounters an error, it stops, leaving node in a borked state.
    pub fn verify_node(
        &mut self,
        mut full_processor: Rc<Processor>,
        mut filtered_processor: Option<Rc<Processor>>,
        cursor: &mut NodeCursor,
        new_premises: &mut HashSet<(ModuleId, String)>,
        mut new_certs: Option<&mut Vec<Certificate>>,
        mut worklist: Option<&mut CertificateWorklist>,
    ) -> Result<(), BuildError> {
        if !cursor.requires_verification() {
            return Ok(());
        }

        if cursor.num_children() > 0 {
            // We need to recurse into children
            cursor.descend(0);
            loop {
                self.verify_node(
                    Rc::clone(&full_processor),
                    filtered_processor.clone(), // cheap clone of Option<Rc<_>>
                    cursor,
                    new_premises,
                    new_certs.as_deref_mut(),
                    worklist.as_deref_mut(),
                )?;

                if let Some(fact) = cursor.node().get_fact() {
                    if let Some(ref mut fp) = filtered_processor {
                        Rc::make_mut(fp).add_fact(fact.clone())?;
                    }
                    Rc::make_mut(&mut full_processor).add_fact(fact)?;
                }

                if cursor.has_next() {
                    cursor.next();
                } else {
                    break;
                }
            }
            cursor.ascend();
        }

        if cursor.node().has_goal() {
            let goal = cursor.goal().unwrap();
            if let Some((_, line)) = self.single_goal {
                if goal.first_line != line {
                    // This isn't the goal we're looking for.
                    return Ok(());
                }
            }
            self.verify_with_fallback(
                full_processor,
                filtered_processor,
                &goal,
                cursor.goal_env().unwrap(),
                new_certs,
                worklist,
                new_premises,
            )?;
        }

        Ok(())
    }

    /// Verifies all goals within this module.
    pub fn verify_module(
        &mut self,
        target: &ModuleDescriptor,
        env: &Environment,
    ) -> Result<(), BuildError> {
        if env.nodes.is_empty() {
            // Nothing to prove
            return Ok(());
        }

        let module_hash = self.project.get_module_hash(env.module_id).unwrap();
        let old_module_cache = self.project.module_caches.get_cloned_module_cache(target);
        let mut new_module_cache = ModuleCache::new(module_hash);

        // If we're using certificates, create a worklist and a vector of new certs.
        let (mut new_certs, mut worklist) = match self.project.build_cache.as_ref() {
            Some(bc) => {
                let worklist = bc.make_worklist(target);
                (Some(vec![]), worklist)
            }
            None => (None, None),
        };

        self.module_proving_started(target.clone());

        // The full processor has access to all imported facts.
        let mut full_processor = Processor::with_token(self.cancellation_token.clone());
        for fact in self.project.imported_facts(env.module_id, None) {
            full_processor.add_fact(fact.clone())?;
        }
        let mut full_processor = Rc::new(full_processor);
        let mut cursor = NodeCursor::new(&env, 0);

        // Loop over all the nodes that are right below the top level.
        loop {
            if cursor.requires_verification() {
                {
                    // We do need to verify this.

                    // If we have a cached set of premises, we use it to create a filtered prover.
                    // The filtered prover only contains the premises that we think it needs.
                    let block_name = cursor.block_name();
                    let filtered_processor =
                        self.make_filtered_processor(env, &block_name, &old_module_cache)?;

                    // The premises we use while verifying this block.
                    let mut new_premises = HashSet::new();

                    // This call will recurse and verify everything within this top-level block.
                    self.verify_node(
                        Rc::clone(&full_processor),
                        filtered_processor,
                        &mut cursor,
                        &mut new_premises,
                        new_certs.as_mut(),
                        worklist.as_mut(),
                    )?;
                    match self
                        .project
                        .normalize_premises(env.module_id, &block_name, &new_premises)
                    {
                        Some(normalized) => {
                            // We verified this block, so we can cache it.
                            new_module_cache
                                .blocks
                                .insert(block_name.clone(), normalized);
                        }
                        None => {
                            // We couldn't normalize the premises, so we can't cache them.
                            // This can happen if the module is unimportable.
                            self.log_global(format!(
                                "could not normalize premises for {}",
                                block_name
                            ));
                        }
                    }
                }
            } else {
                self.log_verified(cursor.node().first_line(), cursor.node().last_line());
            }
            if !cursor.has_next() {
                break;
            }
            if let Some(fact) = cursor.node().get_fact() {
                Rc::make_mut(&mut full_processor).add_fact(fact.clone())?;
            }
            cursor.next();
        }

        if self.module_proving_complete(target) && self.single_goal.is_none() {
            // The module was entirely verified.

            if let Some(worklist) = worklist {
                self.metrics.certs_unused += worklist.unused() as i32;
            }

            if let Some(certs) = new_certs {
                // Insert the new CertificateStore into the build cache
                let cert_store = CertificateStore { certs };
                // Get the content hash for this module
                if let Some(content_hash) = self.project.get_module_content_hash(env.module_id) {
                    self.build_cache.as_mut().unwrap().insert(
                        target.clone(),
                        cert_store,
                        content_hash,
                    );
                }
            }
        }
        Ok(())
    }

    /// Builds all open modules, logging build events.
    pub fn build(&mut self) {
        // Initialize the build cache if we're using certificates
        if self.project.using_certs() {
            self.build_cache = Some(BuildCache::new(self.project.build_dir.clone()));
        }

        // Build in alphabetical order by module name for consistency.
        let mut targets = self.project.targets.iter().collect::<Vec<_>>();
        targets.sort();

        let verification_message = if targets.len() > 5 {
            format!("verifying {} modules...", targets.len())
        } else {
            format!(
                "verifying modules: {}",
                targets
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        self.log_global(verification_message);

        // The first phase is the "loading phase". We load modules and look for errors.
        // If there are errors, we won't try to do proving.
        let mut envs = vec![];
        for target in &targets {
            let module = self.project.get_module(target);
            match module {
                LoadState::Ok(env) => {
                    self.module_loaded(&env);
                    envs.push(env);
                }
                LoadState::Error(e) => {
                    if e.indirect {
                        if self.log_secondary_errors {
                            // The real problem is in a different module.
                            // So we don't want to locate the error in this module.
                            self.log_global(e.to_string());
                        }
                    } else {
                        self.log_loading_error(target, e);
                    }
                }
                LoadState::None => {
                    // Targets are supposed to be loaded already.
                    self.log_global(format!("error: module {} is not loaded", target));
                }
                LoadState::Loading => {
                    // Happens if there's a circular import. A more localized error should
                    // show up elsewhere, so let's just log.
                    self.log_global(format!("error: module {} stuck in loading", target));
                }
            }
        }

        if self.status.is_error() {
            return;
        }

        self.loading_phase_complete();

        // Track the total number of modules to build
        self.metrics.modules_total = envs.len() as i32;

        // The second pass is the "proving phase".
        for (target, env) in targets.into_iter().zip(envs) {
            if let Some((ref m, _)) = self.single_goal {
                if m != target {
                    continue;
                }
            }

            if self.try_skip_unchanged_module(env.module_id, &target) {
                // Update metrics to count the goals in this module as a success
                let goal_count = env.iter_goals().count() as i32;
                self.metrics.goals_done += goal_count;
                self.metrics.goals_success += goal_count;
                self.metrics.certs_cached += goal_count;
                self.metrics.modules_cached += 1;

                let event = BuildEvent {
                    progress: Some((self.metrics.goals_done, self.metrics.goals_total)),
                    ..self.default_event()
                };
                (self.event_handler)(event);

                continue;
            }

            if let Err(e) = self.verify_module(&target, env) {
                self.log_build_error(&e);
                return;
            }
        }
    }

    /// Tries to skip building a module if it and all its dependencies are unchanged.
    /// If successful, copies certificates to the new build cache and returns true.
    /// This only works when check_hashes is true.
    fn try_skip_unchanged_module(
        &mut self,
        module_id: ModuleId,
        target: &ModuleDescriptor,
    ) -> bool {
        if !self.check_hashes {
            return false;
        }

        let Some(build_cache) = &self.project.build_cache else {
            return false;
        };

        let Some(descriptor) = self.project.get_module_descriptor(module_id) else {
            return false;
        };

        let Some(current_hash) = self.project.get_module_content_hash(module_id) else {
            return false;
        };

        if !build_cache.manifest_matches(descriptor, current_hash) {
            return false;
        }

        // Check all dependencies recursively
        for dep_id in self.project.all_dependencies(module_id) {
            let Some(dep_descriptor) = self.project.get_module_descriptor(dep_id) else {
                return false;
            };

            let Some(dep_hash) = self.project.get_module_content_hash(dep_id) else {
                return false;
            };

            if !build_cache.manifest_matches(dep_descriptor, dep_hash) {
                return false;
            }
        }

        let Some(_existing_certs) = build_cache.get_certificates(target) else {
            // This is a bad case. The different build files are inconsistent.
            // Well, just ignore it.
            return false;
        };

        // We verified that certificates exist, but we don't copy them to the new cache.
        // They'll be handled during the merge in update_build_cache.
        // We still need to update the manifest though.
        if let ModuleDescriptor::Name(parts) = target {
            self.build_cache.as_mut().unwrap().manifest.insert(parts, current_hash);
        }

        true
    }

    /// Consumes the builder and returns the build cache if the build was successful
    /// and we should update the cache.
    pub fn into_build_cache(self) -> Option<BuildCache> {
        // There's a lot of conditions for when we actually write to the cache
        if self.project.using_certs()
            && self.status.is_good()
            && self.project.config.write_cache
            && self.single_goal.is_none()
        {
            self.build_cache
        } else {
            None
        }
    }
}
