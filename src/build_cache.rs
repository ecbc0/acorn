use std::collections::HashMap;
use std::error::Error;
use std::path::PathBuf;
use walkdir::WalkDir;

use crate::certificate::{CertificateStore, CertificateWorklist};
use crate::module::ModuleDescriptor;

pub struct BuildCache {
    cache: HashMap<ModuleDescriptor, CertificateStore>,
}

impl BuildCache {
    pub fn new() -> Self {
        BuildCache {
            cache: HashMap::new(),
        }
    }

    /// Load a build cache from a directory containing JSONL files
    pub fn load(directory: &PathBuf) -> Self {
        let mut cache = HashMap::new();
        
        if directory.exists() {
            for entry in WalkDir::new(directory).into_iter().filter_map(Result::ok) {
                let path = entry.path();
                if path.extension().and_then(|ext| ext.to_str()) == Some("jsonl") {
                    if let Some((desc, cert_store)) = CertificateStore::load_relative(directory, path) {
                        cache.insert(desc, cert_store);
                    }
                }
            }
        }
        
        BuildCache { cache }
    }

    pub fn insert(&mut self, module: ModuleDescriptor, certificates: CertificateStore) {
        self.cache.insert(module, certificates);
    }

    pub fn make_worklist(&self, descriptor: &ModuleDescriptor) -> Option<CertificateWorklist> {
        self.cache
            .get(descriptor)
            .map(|store| CertificateWorklist::new(store.clone()))
    }

    pub fn save(&self, directory: PathBuf) -> Result<(), Box<dyn Error>> {
        for (descriptor, cert_store) in &self.cache {
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
                cert_store.save(&path)?;
            }
        }
        Ok(())
    }
}
