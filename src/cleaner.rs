use std::path::PathBuf;

use tower_lsp::lsp_types::Range;

use crate::block::Node;
use crate::environment::Environment;
use crate::module::{LoadState, ModuleDescriptor};
use crate::project::{ImportError, Project, ProjectConfig, ProjectError};

/// A Cleaner analyzes loaded modules to extract information about claims and proofs.
/// It doesn't store state - each operation loads a fresh Project.
pub struct Cleaner {}

/// Errors that can occur when using the Cleaner.
#[derive(Debug)]
pub enum CleanerError {
    Project(ProjectError),
    Import(ImportError),
    ModuleNotLoaded,
    ModuleLoading,
}

impl From<ProjectError> for CleanerError {
    fn from(error: ProjectError) -> Self {
        CleanerError::Project(error)
    }
}

impl From<ImportError> for CleanerError {
    fn from(error: ImportError) -> Self {
        CleanerError::Import(error)
    }
}

impl Cleaner {
    /// Creates a new Cleaner.
    pub fn new(project_root: PathBuf, module_spec: ModuleDescriptor) -> Self {
        Cleaner {}
    }

    /// Returns the ranges of all Node::Claim nodes in the specified module,
    /// in preorder traversal order. Recurses into blocks but doesn't report
    /// the blocks themselves.
    ///
    /// Loads a fresh Project each time to ensure it picks up any changes.
    pub fn claim_ranges(
        &self,
        project_root: PathBuf,
        module_spec: ModuleDescriptor,
    ) -> Result<Vec<Range>, CleanerError> {
        // Load a fresh project
        let config = ProjectConfig {
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
        };
        let mut project = Project::new_local(project_root.as_path(), config)?;

        // Load the module
        let module_id = project.load_module_by_name(&module_spec.to_string())?;
        let module_state = project.get_module_by_id(module_id);

        // Get the environment from the loaded module
        let env = match module_state {
            LoadState::Ok(env) => env,
            LoadState::Error(_) => {
                // If there's a compilation error, we still want to extract what we can
                // Return empty ranges for now
                return Ok(Vec::new());
            }
            LoadState::Loading => return Err(CleanerError::ModuleLoading),
            LoadState::None => return Err(CleanerError::ModuleNotLoaded),
        };

        // Collect claim ranges
        let mut ranges = Vec::new();
        Self::collect_claim_ranges(env, &mut ranges);
        Ok(ranges)
    }

    /// Recursively collects claim ranges from an environment and all nested blocks.
    fn collect_claim_ranges(env: &Environment, ranges: &mut Vec<Range>) {
        for node in &env.nodes {
            match node {
                Node::Claim(prop) => {
                    // Add this claim's range
                    ranges.push(prop.source.range);
                }
                Node::Block(block, _) => {
                    // Recurse into the block's environment
                    Self::collect_claim_ranges(&block.env, ranges);
                }
                Node::Structural(_) => {
                    // Skip structural nodes
                }
            }
        }
    }
}
