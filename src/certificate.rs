use serde::{Deserialize, Serialize};
use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

use crate::module::ModuleDescriptor;

/// A proof certificate containing the concrete proof steps
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Certificate {
    /// The name of the goal that was proved
    pub goal: String,

    /// The proof steps as strings.
    /// None indicates no proof exists for this goal.
    /// This is useful as a placeholder to indicate that we need to find a proof.
    /// Some(vec![]) indicates a trivial proof requiring no steps.
    pub proof: Option<Vec<String>>,
}

impl Certificate {
    /// Create a new certificate with proof steps
    pub fn new(goal: String, proof: Vec<String>) -> Self {
        Certificate {
            goal,
            proof: Some(proof),
        }
    }

    /// Create a placeholder certificate with no proof
    pub fn placeholder(goal: String) -> Self {
        Certificate { goal, proof: None }
    }

    /// Check if this certificate has a proof
    pub fn has_proof(&self) -> bool {
        self.proof.is_some()
    }
}

/// A collection of certificates that can be saved to a file
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct CertificateStore {
    pub certs: Vec<Certificate>,
}

impl CertificateStore {
    /// Load a certificate store from a file in JSONL format (one certificate per line)
    pub fn load(filename: &Path) -> Result<CertificateStore, Box<dyn Error>> {
        let file = File::open(filename)?;
        let reader = BufReader::new(file);
        let mut certs = Vec::new();

        for line in reader.lines() {
            let line = line?;
            if !line.trim().is_empty() {
                let cert: Certificate = serde_json::from_str(&line)?;
                certs.push(cert);
            }
        }

        Ok(CertificateStore { certs })
    }

    /// Save the certificate store to a file in JSONL format (one certificate per line)
    pub fn save(&self, filename: &Path) -> Result<(), Box<dyn Error>> {
        let file = File::create(filename)?;
        let mut writer = BufWriter::new(file);

        for cert in &self.certs {
            let json = serde_json::to_string(cert)?;
            writeln!(writer, "{}", json)?;
        }

        writer.flush()?;
        Ok(())
    }

    /// Loads a CertificateStore along with its descriptor.
    /// Similar to ModuleCache::load_relative, this expects certificate files to have .jsonl extension
    pub fn load_relative(
        root: &Path,
        full_filename: &Path,
    ) -> Option<(ModuleDescriptor, CertificateStore)> {
        let relative_filename = full_filename.strip_prefix(root).ok()?;
        let ext = relative_filename.extension()?;
        if ext != "jsonl" {
            return None;
        }
        let path_without_extension = relative_filename.with_extension("");
        let parts = path_without_extension
            .components()
            .map(|c| c.as_os_str().to_string_lossy().to_string())
            .collect::<Vec<_>>();
        let descriptor = ModuleDescriptor::Name(parts);
        let cert_store = CertificateStore::load(full_filename).ok()?;
        Some((descriptor, cert_store))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_save_load_cycle() {
        // Create a temporary directory for testing
        let temp_dir = tempdir().unwrap();
        let file_path = temp_dir.path().join("test_certs.jsonl");

        // Create some test certificates
        let cert1 = Certificate::new(
            "goal1".to_string(),
            vec!["step1".to_string(), "step2".to_string()],
        );
        let cert2 = Certificate::new(
            "goal2".to_string(),
            vec![
                "step3".to_string(),
                "step4".to_string(),
                "step5".to_string(),
            ],
        );
        let cert3 = Certificate::new(
            "goal3".to_string(),
            vec![], // Trivial proof with no steps
        );
        let cert4 = Certificate::placeholder(
            "goal4".to_string(), // No proof exists for this goal
        );

        // Create original certificate store
        let original = CertificateStore {
            certs: vec![cert1, cert2, cert3, cert4],
        };

        // Save to file
        original.save(&file_path).unwrap();

        // Load from file
        let loaded = CertificateStore::load(&file_path).unwrap();

        // Check that we got the same data back
        assert_eq!(original.certs.len(), loaded.certs.len());

        for (orig, load) in original.certs.iter().zip(loaded.certs.iter()) {
            assert_eq!(orig.goal, load.goal);
            assert_eq!(orig.proof, load.proof);
        }

        // Test has_proof() helper on loaded certificates
        assert!(loaded.certs[0].has_proof());
        assert!(loaded.certs[1].has_proof());
        assert!(loaded.certs[2].has_proof());
        assert!(!loaded.certs[3].has_proof());

        // Clean up is automatic when temp_dir goes out of scope
    }
}
