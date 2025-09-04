use std::path::PathBuf;

use crate::block::NodeCursor;
use crate::project::{Project, ProjectConfig};
use crate::prover::Outcome;

pub struct Searcher {
    /// The target module or file to search in.
    target: String,

    /// The line number to search at (1-based, as provided by the user).
    line_number: u32,

    /// The starting path to find the acorn library from.
    start_path: PathBuf,
}

impl Searcher {
    pub fn new(start_path: PathBuf, target: String, line_number: u32) -> Self {
        Self {
            target,
            line_number,
            start_path,
        }
    }

    /// Runs the search and returns an error string if the search fails.
    pub fn run(&self) -> Result<(), String> {
        let config = ProjectConfig {
            check_hashes: false,
            ..Default::default()
        };
        let mut project = match Project::new_local(&self.start_path, config) {
            Ok(p) => p,
            Err(e) => return Err(format!("Error: {}", e)),
        };

        // Convert from 1-based (external) to 0-based (internal) line number
        let internal_line_number = self.line_number - 1;

        let module_id = project
            .load_module_by_name(&self.target)
            .map_err(|e| format!("Failed to load module '{}': {}", self.target, e))?;

        let env = project
            .get_env_by_id(module_id)
            .ok_or_else(|| format!("No environment found for module '{}'", self.target))?;

        let path = env.path_for_line(internal_line_number).map_err(|s| {
            format!(
                "no proposition for line {} in {}: {}",
                self.line_number, self.target, s
            )
        })?;

        let cursor = NodeCursor::from_path(env, &path);
        let goal_context = cursor.goal().map_err(|e| {
            format!(
                "Error getting goal at line {} in {}: {}",
                self.line_number, self.target, e
            )
        })?;

        println!("proving {} ...", goal_context.name);

        let verbose = false;
        // Try to use the filtered prover
        let module_descriptor = project
            .get_module_descriptor(module_id)
            .ok_or_else(|| format!("Module {} not found", module_id))?;
        let module_cache = project.get_module_cache(module_descriptor);

        let block_name = cursor.block_name();
        let mut prover = match project.make_filtered_prover(env, &block_name, &module_cache) {
            Some(mut filtered_prover) => {
                println!("using filtered prover");
                for fact in cursor.block_facts() {
                    filtered_prover.add_fact(fact);
                }
                filtered_prover
            }
            None => {
                return Err(format!(
                    "Cannot create filtered prover: no cached premises found for {} at line {}. \
                        Run verification in standard mode first to build the cache.",
                    block_name, self.line_number
                ));
            }
        };

        prover.verbose = verbose;
        prover.strict_codegen = true;
        prover.set_goal(&goal_context);

        loop {
            let outcome = prover.partial_search();

            match outcome {
                Outcome::Success => {
                    println!("success!");
                    let env = cursor.goal_env().unwrap();
                    if let Err(e) = prover.make_cert(&project, &env.bindings, true) {
                        println!("Error generating concrete proof: {}", e);
                    }
                }
                Outcome::Inconsistent => {
                    println!("Found inconsistency!");
                    prover.get_and_print_proof(&project, &env.bindings);
                }
                Outcome::Exhausted => {
                    println!("All possibilities have been exhausted.");
                }
                Outcome::Timeout => {
                    println!("activated {} steps", prover.num_activated());
                    continue;
                }
                Outcome::Interrupted => {
                    println!("Interrupted.");
                }
                Outcome::Constrained => {
                    println!("Constrained.");
                }
                Outcome::Error(s) => {
                    println!("Error: {}", s);
                }
            }

            break;
        }

        Ok(())
    }
}
