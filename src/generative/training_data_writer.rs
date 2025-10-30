use std::fs::{self, File};
use std::io::{self, BufWriter, Write};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};

use super::goal_context::GoalContext;
use crate::certificate::Certificate;

/// Manages writing training data proofs to numbered files in a directory.
pub struct TrainingDataWriter {
    output_dir: PathBuf,
    counter: AtomicU32,
}

impl TrainingDataWriter {
    /// Creates a new TrainingDataWriter for the specified directory.
    ///
    /// If the directory doesn't exist, it will be created.
    /// If it exists and contains only .txt files, they will be deleted.
    /// If it contains non-.txt files, returns an error.
    pub fn new(dir: &str) -> Result<Self, String> {
        let output_dir = PathBuf::from(dir);

        if output_dir.exists() {
            if !output_dir.is_dir() {
                return Err(format!("Error: '{}' exists but is not a directory", dir));
            }

            // Check all files in the directory
            let entries = fs::read_dir(&output_dir)
                .map_err(|e| format!("Error reading directory '{}': {}", dir, e))?;

            let mut txt_files = Vec::new();
            let mut non_txt_files = Vec::new();

            for entry in entries {
                let entry = entry.map_err(|e| format!("Error reading directory entry: {}", e))?;
                let path = entry.path();

                if path.is_file() {
                    if path.extension().and_then(|s| s.to_str()) == Some("txt") {
                        txt_files.push(path);
                    } else {
                        non_txt_files.push(path);
                    }
                }
            }

            if !non_txt_files.is_empty() {
                return Err(format!(
                    "Error: directory '{}' contains non-.txt files. Please specify an empty directory or one containing only .txt files.",
                    dir
                ));
            }

            // Delete all .txt files
            if !txt_files.is_empty() {
                for file in &txt_files {
                    fs::remove_file(file)
                        .map_err(|e| format!("Error deleting file '{}': {}", file.display(), e))?;
                }
                println!(
                    "Cleaned up {} existing .txt files from '{}'",
                    txt_files.len(),
                    dir
                );
            }
        } else {
            // Create the directory
            fs::create_dir_all(&output_dir)
                .map_err(|e| format!("Error creating directory '{}': {}", dir, e))?;
            println!("Created training data directory: {}", dir);
        }

        Ok(TrainingDataWriter {
            output_dir,
            counter: AtomicU32::new(0),
        })
    }

    /// Writes a proof to the next numbered file.
    /// Returns the path of the created file.
    pub fn write_proof(&self, context: &GoalContext, cert: &Certificate) -> io::Result<PathBuf> {
        let index = self.counter.fetch_add(1, Ordering::SeqCst);
        let filename = format!("proof_{:05}.txt", index);
        let filepath = self.output_dir.join(&filename);

        let file = File::create(&filepath)?;
        let mut writer = BufWriter::new(file);

        // Write the goal context
        context.write_to(&mut writer)?;

        // Write the proof
        cert.write_proof_to(&mut writer)?;

        // Flush to ensure everything is written
        writer.flush()?;

        Ok(filepath)
    }

    /// Returns the number of proofs written so far.
    pub fn count(&self) -> u32 {
        self.counter.load(Ordering::SeqCst)
    }
}
