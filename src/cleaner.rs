use std::io;
use std::path::PathBuf;

use tower_lsp::lsp_types::Range;

use crate::block::Node;
use crate::environment::Environment;
use crate::module::{LoadState, ModuleDescriptor};
use crate::project::{ImportError, Project, ProjectConfig, ProjectError};
use crate::verifier::Verifier;

/// A Cleaner analyzes loaded modules to extract information about claims and proofs.
/// It stores the project root and module spec, but loads fresh Projects for each operation.
pub struct Cleaner {
    project_root: PathBuf,
    module_spec: ModuleDescriptor,
}

/// Statistics from a cleaning operation.
#[derive(Debug)]
pub struct CleanStats {
    pub claims_deleted: usize,
    pub claims_kept: usize,
    pub original_lines: usize,
    pub final_lines: usize,
}

/// Errors that can occur when using the Cleaner.
#[derive(Debug)]
pub enum CleanerError {
    Project(ProjectError),
    Import(ImportError),
    ModuleNotLoaded,
    ModuleLoading,
    Io(io::Error),
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

impl From<io::Error> for CleanerError {
    fn from(error: io::Error) -> Self {
        CleanerError::Io(error)
    }
}

impl Cleaner {
    /// Creates a new Cleaner for the specified project and module.
    pub fn new(project_root: PathBuf, module_spec: ModuleDescriptor) -> Self {
        Cleaner {
            project_root,
            module_spec,
        }
    }

    /// Returns the ranges of all cleanable nodes in the specified module,
    /// including both Node::Claim nodes and Node::Block nodes with source ranges.
    /// Returns ranges in preorder traversal order.
    ///
    /// Loads a fresh Project each time to ensure it picks up any changes.
    pub fn ranges(&self) -> Result<Vec<Range>, CleanerError> {
        // Load a fresh project
        let config = ProjectConfig {
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
        };
        let mut project = Project::new_local(self.project_root.as_path(), config)?;

        // Load the module
        let module_id = project.load_module_by_name(&self.module_spec.to_string())?;
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

        // Collect ranges from the module environment (depth 0)
        let mut ranges = Vec::new();
        Self::collect_ranges(env, &mut ranges);
        Ok(ranges)
    }

    /// Recursively collects cleanable ranges from an environment.
    /// This includes both Claim nodes and Block nodes with source ranges.
    /// Only collects items inside proofs (env.depth >= 1), never top-level items.
    /// - depth 0: top-level module (not cleanable - might be imported)
    /// - depth 1+: inside theorem/axiom proof blocks (cleanable - local to proof)
    fn collect_ranges(env: &Environment, ranges: &mut Vec<Range>) {
        // Only collect ranges when we're inside a proof (depth >= 1)
        let inside_proof = env.depth >= 1;

        for node in &env.nodes {
            match node {
                Node::Claim(prop) => {
                    // Only collect claims when inside proofs
                    if inside_proof {
                        ranges.push(prop.source.range);
                    }
                }
                Node::Block(block, _) => {
                    // Only collect blocks when inside proofs
                    // This means forall/if/by blocks inside theorems are cleanable,
                    // but top-level theorem blocks themselves are not
                    if inside_proof {
                        if let Some(range) = block.source_range {
                            ranges.push(range);
                        }
                    }
                    // Always recurse into the block to find nested cleanable items
                    Self::collect_ranges(&block.env, ranges);
                }
                Node::Structural(_) => {
                    // Skip structural nodes
                }
            }
        }
    }

    /// Attempts to delete the lines in the given range from the module file.
    /// If the module still verifies after deletion, returns Ok(true) and keeps the deletion.
    /// If verification fails (including parse errors), restores the original file and returns Ok(false).
    /// Returns Err only for unexpected errors (file not found, permission issues, etc.).
    ///
    /// # Panics
    /// Panics if the range is invalid (start line beyond file bounds), which indicates a bug in the caller.
    pub fn try_delete(&self, range: Range) -> Result<bool, CleanerError> {
        // Get the file path
        let config = ProjectConfig {
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
        };
        let project = Project::new_local(self.project_root.as_path(), config)?;
        let file_path = project.path_from_descriptor(&self.module_spec)?;

        // Read the original file content
        let original_content = std::fs::read_to_string(&file_path)?;

        // Delete the lines in the range
        let lines: Vec<&str> = original_content.lines().collect();
        let start_line = range.start.line as usize;
        let end_line = range.end.line as usize;

        // Validate range - panic if invalid since this indicates a bug
        assert!(
            start_line < lines.len(),
            "Range start line {} is beyond file bounds (file has {} lines)",
            start_line,
            lines.len()
        );

        // Build new content without the deleted lines
        let mut new_lines = Vec::new();
        for (i, line) in lines.iter().enumerate() {
            if i < start_line || i > end_line {
                new_lines.push(*line);
            }
        }
        let new_content = new_lines.join("\n");
        // Add trailing newline if original had one
        let new_content = if original_content.ends_with('\n') {
            format!("{}\n", new_content)
        } else {
            new_content
        };

        // Write the modified content to disk
        std::fs::write(&file_path, &new_content)?;

        // Try to verify the module
        let verification_result = match Verifier::new(
            self.project_root.clone(),
            ProjectConfig::default(),
            Some(self.module_spec.to_string()),
        ) {
            Ok(mut verifier) => {
                // Enable early exit on warning - no need to continue verifying once we hit any issue
                verifier.exit_on_warning = true;
                // Run verification
                match verifier.run() {
                    Ok(output) => output.is_success(),
                    Err(_) => false, // Treat verification errors as failure
                }
            }
            Err(_) => false, // Treat initialization errors as failure (e.g., parse errors)
        };

        // If verification failed, restore the original file
        if !verification_result {
            std::fs::write(&file_path, original_content)?;
            return Ok(false);
        }

        // Verification succeeded - keep the deletion
        Ok(true)
    }

    /// Iteratively removes redundant claims from the module.
    /// Returns statistics about the cleaning operation.
    pub fn clean(&self) -> Result<CleanStats, CleanerError> {
        // Count original lines
        let original_lines = self.count_lines()?;

        let mut claims_deleted = 0;
        let mut claims_kept = 0;
        let mut last_required_range: Option<Range> = None;

        loop {
            // Get current cleanable ranges
            let ranges = self.ranges()?;

            // Find the first claim range that comes after last_required_range
            let next_range = ranges.iter().find(|range| {
                if let Some(ref last_req) = last_required_range {
                    range.start.line > last_req.start.line
                } else {
                    true // No last required, so first range is next
                }
            });

            // If no more claims to try, we're done
            let Some(&range_to_try) = next_range else {
                break;
            };

            // Calculate how many goals are already cleaned (skipped/processed)
            // This is the number we've already decided on (deleted or kept)
            let goals_cleaned = claims_deleted + claims_kept;
            let total_goals = goals_cleaned + ranges.len();
            println!("{}/{} goals cleaned", goals_cleaned, total_goals);

            // Try to delete this claim
            if self.try_delete(range_to_try)? {
                // Deletion succeeded
                claims_deleted += 1;
                // Continue loop - ranges will be recalculated
            } else {
                // Deletion failed - this claim is required
                last_required_range = Some(range_to_try);
                claims_kept += 1;
                // Continue to next claim
            }
        }

        // Count final lines
        let final_lines = self.count_lines()?;

        // Final verification: verify the entire project (not just the module)
        // If this fails, there's a bug in the cleaning algorithm
        println!("Running final verification on entire project...");
        let final_verification_result = match Verifier::new(
            self.project_root.clone(),
            ProjectConfig::default(),
            None, // Verify all modules, not just this one
        ) {
            Ok(verifier) => {
                // Don't enable early exit here - we want to see all issues if there are any
                match verifier.run() {
                    Ok(output) => output.is_success(),
                    Err(e) => {
                        println!("Final verification failed with error: {}", e);
                        false
                    }
                }
            }
            Err(e) => {
                println!("Failed to initialize final verification: {}", e);
                false
            }
        };

        if !final_verification_result {
            return Err(CleanerError::Project(crate::project::ProjectError(
                "BUG: Final verification failed after cleaning. This indicates a bug in the cleaning algorithm.".to_string(),
            )));
        }

        let stats = CleanStats {
            claims_deleted,
            claims_kept,
            original_lines,
            final_lines,
        };

        // Print stats
        println!("Cleaning complete!");
        println!("  Claims deleted: {}", stats.claims_deleted);
        println!("  Claims kept: {}", stats.claims_kept);
        println!(
            "  Lines: {} -> {} (removed {} lines)",
            stats.original_lines,
            stats.final_lines,
            stats.original_lines - stats.final_lines
        );

        Ok(stats)
    }

    /// Counts the number of lines in the module file.
    fn count_lines(&self) -> Result<usize, CleanerError> {
        let config = ProjectConfig {
            use_filesystem: true,
            read_cache: true,
            write_cache: false,
        };
        let project = Project::new_local(self.project_root.as_path(), config)?;
        let file_path = project.path_from_descriptor(&self.module_spec)?;
        let content = std::fs::read_to_string(&file_path)?;
        Ok(content.lines().count())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use indoc::indoc;
    use std::fs;
    use tempfile::TempDir;

    /// Helper function to clean Acorn code and return the result.
    /// Creates a temporary project, writes the input code, runs the cleaner, and returns the cleaned code.
    fn clean(input: &str) -> String {
        // Create a test project
        let temp_dir = TempDir::new().unwrap();
        let src_dir = temp_dir.path().join("src");
        fs::create_dir(&src_dir).unwrap();
        let toml_file = temp_dir.path().join("acorn.toml");
        fs::write(&toml_file, "").unwrap();

        // Create the test file
        let test_file = src_dir.join("test.ac");
        fs::write(&test_file, input).unwrap();

        // Create a cleaner for this module
        let cleaner = Cleaner::new(
            temp_dir.path().to_path_buf(),
            ModuleDescriptor::name("test"),
        );

        // Run the cleaning operation
        cleaner.clean().expect("cleaning should succeed");

        // Read and return the cleaned file
        let output = fs::read_to_string(&test_file).unwrap();
        println!("Cleaned content:\n{}", output);
        output
    }

    #[test]
    fn test_cleaning_partial() {
        let input = indoc! {r#"
            inductive Color {
                red
                blue
            }

            axiom foo(f: Color -> Bool, c: Color) {
                f(c)
            }

            theorem cheat(c: Color) {
                c = Color.red
            } by {
                Color.red != Color.blue
                define f(d: Color) -> Bool {
                    d = Color.red
                }
                Color.red != Color.blue
                foo(f, c)
                Color.red != Color.blue
            }
        "#};

        let output = clean(input);

        // The core theorem structure should be preserved
        assert!(output.contains("theorem cheat"));
        assert!(output.contains(indoc! {r#"
            theorem cheat(c: Color) {
                c = Color.red
            } by {
                define f(d: Color) -> Bool {
                    d = Color.red
                }
                foo(f, c)
            }"#}));
    }

    #[test]
    fn test_cleaning_full() {
        let input = indoc! {r#"
            inductive Color {
                red
                blue
            }

            let fav: Color = Color.red

            theorem possibilities(c: Color) {
                c = Color.red or c = Color.blue
            } by {
                forall(d: Color) {
                    true
                }
                Color.red != Color.blue
            }
        "#};

        let output = clean(input);

        // Most stuff should be preserved
        assert!(output.contains("theorem possibilities"));
        assert!(output.contains("let fav"));
        assert!(output.contains("inductive Color"));

        // All the "by" blocks should be cleaned
        assert!(!output.contains("by"));
    }
}
