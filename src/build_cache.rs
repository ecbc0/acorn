use std::collections::HashMap;
use std::error::Error;
use std::path::PathBuf;
use walkdir::WalkDir;

use crate::certificate::{CertificateStore, CertificateWorklist};
use crate::manifest::Manifest;
use crate::module::ModuleDescriptor;

/// Cached information about a successful build.
/// Stored in the 'build' directory.
pub struct BuildCache {
    cache: HashMap<ModuleDescriptor, CertificateStore>,
    pub manifest: Manifest,
    build_dir: PathBuf,
}

impl BuildCache {
    pub fn new(build_dir: PathBuf) -> Self {
        BuildCache {
            cache: HashMap::new(),
            manifest: Manifest::new(),
            build_dir,
        }
    }

    /// Load a build cache from a directory containing JSONL files
    pub fn load(build_dir: PathBuf) -> Self {
        let mut cache = HashMap::new();

        if build_dir.exists() {
            for entry in WalkDir::new(&build_dir).into_iter().filter_map(Result::ok) {
                let path = entry.path();
                if path.extension().and_then(|ext| ext.to_str()) == Some("jsonl") {
                    if let Some((desc, cert_store)) =
                        CertificateStore::load_relative(&build_dir, path)
                    {
                        cache.insert(desc, cert_store);
                    }
                }
            }
        }

        let manifest = Manifest::load_or_create(&build_dir);

        BuildCache { 
            cache, 
            manifest,
            build_dir,
        }
    }

    pub fn insert(
        &mut self,
        module: ModuleDescriptor,
        certificates: CertificateStore,
        hash: blake3::Hash,
    ) {
        // Update the certificate cache
        self.cache.insert(module.clone(), certificates);

        // Update the manifest with the module hash
        if let ModuleDescriptor::Name(parts) = &module {
            self.manifest.insert(parts, hash);
        }
    }

    pub fn make_worklist(&self, descriptor: &ModuleDescriptor) -> Option<CertificateWorklist> {
        self.cache
            .get(descriptor)
            .map(|store| CertificateWorklist::new(store.clone()))
    }

    pub fn get_certificates(&self, descriptor: &ModuleDescriptor) -> Option<&CertificateStore> {
        self.cache.get(descriptor)
    }

    pub fn manifest_matches(&self, descriptor: &ModuleDescriptor, hash: blake3::Hash) -> bool {
        match descriptor {
            ModuleDescriptor::Name(parts) => self.manifest.matches_entry(parts, hash),
            _ => false,  // Anonymous modules can't be in the manifest
        }
    }


    /// Save the build cache and merge with an old cache.
    /// This:
    /// 1. Merges the old manifest to preserve entries for unchanged modules
    /// 2. Saves only the new certificate files (in self.cache)
    /// 3. Merges the old certificates back so they're available in memory
    pub fn save_and_merge(&mut self, old_cache: &BuildCache) -> Result<(), Box<dyn Error>> {
        // First merge the old manifest to have complete module list
        self.manifest.merge_from(&old_cache.manifest);

        // Save - only writes JSONL files for modules in self.cache
        self.save()?;

        // After saving, merge the old certificates so they're available in memory
        for (descriptor, cert_store) in &old_cache.cache {
            if !self.cache.contains_key(descriptor) {
                self.cache.insert(descriptor.clone(), cert_store.clone());
            }
        }

        Ok(())
    }

    pub fn save(&self) -> Result<(), Box<dyn Error>> {
        // Save only the certificate stores that are in this cache
        // (these are the ones that were actually built/changed)
        for (descriptor, cert_store) in &self.cache {
            match descriptor {
                ModuleDescriptor::Name(parts) => {
                    if parts.is_empty() {
                        continue;
                    }
                    let mut parts = parts.clone();
                    let last = parts.pop().unwrap();
                    let mut path = self.build_dir.clone();

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
                ModuleDescriptor::File(ac_path) => {
                    // For files outside the library, save the JSONL file alongside the .ac file
                    if ac_path.extension() == Some(std::ffi::OsStr::new("ac")) {
                        let jsonl_path = ac_path.with_extension("jsonl");
                        cert_store.save(&jsonl_path)?;
                    }
                }
                ModuleDescriptor::Anonymous => {
                    // Anonymous modules don't get saved
                }
            }
        }

        // Save the manifest
        self.manifest.save(&self.build_dir)?;

        Ok(())
    }
}
