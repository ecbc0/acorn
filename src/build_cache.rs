use std::collections::HashMap;
use std::error::Error;
use std::path::PathBuf;

use crate::certificate::CertificateSet;
use crate::module::ModuleDescriptor;

pub struct BuildCache {
    cache: HashMap<ModuleDescriptor, CertificateSet>,
}

impl BuildCache {
    pub fn new() -> Self {
        BuildCache {
            cache: HashMap::new(),
        }
    }

    pub fn insert(&mut self, module: ModuleDescriptor, certificates: CertificateSet) {
        self.cache.insert(module, certificates);
    }

    pub fn save(&self, directory: PathBuf) -> Result<(), Box<dyn Error>> {
        for (descriptor, cert_set) in &self.cache {
            if let ModuleDescriptor::Name(parts) = descriptor {
                if parts.is_empty() {
                    continue;
                }
                let mut parts = parts.clone();
                let last = parts.pop().unwrap();
                let mut path = directory.clone();
                
                // Create directory structure for nested modules
                for part in parts {
                    path.push(part);
                    if !path.exists() {
                        std::fs::create_dir(&path)?;
                    }
                }
                
                // Create the JSONL file for this module's certificates
                path.push(format!("{}.jsonl", last));
                cert_set.save(&path)?;
            }
        }
        Ok(())
    }
}
