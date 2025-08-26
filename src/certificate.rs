use serde::{Deserialize, Serialize};
use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

/// A proof certificate containing the concrete proof steps
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Certificate {
    /// The name of the goal that was proved
    pub goal: String,
    /// The proof steps as strings
    /// None indicates no proof exists for this goal
    /// Some(vec![]) indicates a trivial proof requiring no steps
    pub proof: Option<Vec<String>>,
}

impl Certificate {
    /// Create a new certificate from proof steps
    pub fn new(goal: String, proof: Option<Vec<String>>) -> Self {
        Certificate { goal, proof }
    }
}

/// A collection of certificates that can be saved to a file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateSet {
    pub certs: Vec<Certificate>,
}

impl CertificateSet {
    /// Load a certificate set from a file in JSONL format (one certificate per line)
    pub fn load(filename: &Path) -> Result<CertificateSet, Box<dyn Error>> {
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
        
        Ok(CertificateSet { certs })
    }
    
    /// Save the certificate set to a file in JSONL format (one certificate per line)
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
            Some(vec!["step1".to_string(), "step2".to_string()])
        );
        let cert2 = Certificate::new(
            "goal2".to_string(), 
            Some(vec!["step3".to_string(), "step4".to_string(), "step5".to_string()])
        );
        let cert3 = Certificate::new(
            "goal3".to_string(),
            Some(vec![])  // Trivial proof with no steps
        );
        let cert4 = Certificate::new(
            "goal4".to_string(),
            None  // No proof exists for this goal
        );
        
        // Create original certificate set
        let original = CertificateSet {
            certs: vec![cert1, cert2, cert3, cert4],
        };
        
        // Save to file
        original.save(&file_path).unwrap();
        
        // Load from file
        let loaded = CertificateSet::load(&file_path).unwrap();
        
        // Check that we got the same data back
        assert_eq!(original.certs.len(), loaded.certs.len());
        
        for (orig, load) in original.certs.iter().zip(loaded.certs.iter()) {
            assert_eq!(orig.goal, load.goal);
            assert_eq!(orig.proof, load.proof);
        }
        
        // Clean up is automatic when temp_dir goes out of scope
    }
}