use std::collections::HashMap;

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
}