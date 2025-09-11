use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

/// A newtype wrapper for module names, created by joining parts with "."
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ModuleName(String);

impl ModuleName {
    /// Create a ModuleName from parts by joining with "."
    pub fn new(parts: &[String]) -> Self {
        ModuleName(parts.join("."))
    }

    /// Get the underlying string
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for ModuleName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A newtype wrapper for hex-encoded hashes
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HexHash(String);

impl HexHash {
    /// Create a HexHash from a blake3::Hash
    pub fn new(hash: blake3::Hash) -> Self {
        HexHash(hash.to_hex().to_string())
    }

    /// Get the underlying hex string
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for HexHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The manifest structure that stores module hashes
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Manifest {
    /// Version of the manifest format
    pub version: u32,

    /// Map from module names to their content hashes
    pub modules: BTreeMap<ModuleName, HexHash>,
}

impl Manifest {
    /// Create a new empty manifest with the current version
    pub fn new() -> Self {
        Manifest {
            version: 1,
            modules: BTreeMap::new(),
        }
    }

    /// Add or update a module hash in the manifest
    pub fn insert(&mut self, parts: &[String], hash: blake3::Hash) {
        let module_name = ModuleName::new(parts);
        let hex_hash = HexHash::new(hash);
        self.modules.insert(module_name, hex_hash);
    }

    /// Check if an entry matches the given module and hash
    pub fn matches_entry(&self, parts: &[String], hash: blake3::Hash) -> bool {
        let module_name = ModuleName::new(parts);
        match self.modules.get(&module_name) {
            Some(stored_hash) => stored_hash == &HexHash::new(hash),
            None => false,
        }
    }

    /// Check if a module exists in the manifest (regardless of hash)
    pub fn contains(&self, parts: &[String]) -> bool {
        let module_name = ModuleName::new(parts);
        self.modules.contains_key(&module_name)
    }

    /// Save the manifest to manifest.json in the cache directory atomically
    /// Writes to a temporary file first, then renames it to avoid corruption
    pub fn save(&self, cache_dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
        let path = cache_dir.join("manifest.json");
        let json = serde_json::to_string_pretty(&self)?;
        
        // Create a temporary file in the same directory as the target
        let temp_path = cache_dir.join(".manifest.json.tmp");
        
        // Write to the temporary file
        let mut file = File::create(&temp_path)?;
        file.write_all(json.as_bytes())?;
        file.sync_all()?; // Ensure data is flushed to disk
        
        // Atomically rename the temp file to the target path
        std::fs::rename(&temp_path, path)?;
        
        Ok(())
    }

    /// Load a manifest from manifest.json in the cache directory
    pub fn load(cache_dir: &Path) -> Result<Self, Box<dyn std::error::Error>> {
        let path = cache_dir.join("manifest.json");
        let mut file = File::open(path)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        let manifest = serde_json::from_str(&contents)?;
        Ok(manifest)
    }

    /// Load a manifest from the cache directory, or create a new one if it doesn't exist
    pub fn load_or_create(cache_dir: &Path) -> Self {
        match Self::load(cache_dir) {
            Ok(manifest) => manifest,
            Err(_) => Self::new(),
        }
    }
}

impl Default for Manifest {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_manifest_save_load() {
        let temp_dir = tempdir().expect("Failed to create temp directory");
        let cache_dir = temp_dir.path();

        let mut manifest = Manifest::new();

        // Add some test data
        let parts = vec!["test".to_string(), "module".to_string()];
        let hash = blake3::hash(b"test content");
        manifest.insert(&parts, hash);

        // Save the manifest
        manifest
            .save(cache_dir)
            .expect("Failed to save manifest");

        // Load it back
        let loaded = Manifest::load(cache_dir).expect("Failed to load manifest");

        // Verify it matches
        assert_eq!(loaded.version, manifest.version);
        assert_eq!(loaded.modules.len(), 1);
        assert!(loaded.matches_entry(&parts, hash));
        
        // Test load_or_create with existing manifest
        let loaded2 = Manifest::load_or_create(cache_dir);
        assert_eq!(loaded2.modules.len(), 1);
        
        // Test load_or_create with non-existent directory
        let new_dir = temp_dir.path().join("nonexistent");
        let created = Manifest::load_or_create(&new_dir);
        assert_eq!(created.modules.len(), 0);
    }
}
