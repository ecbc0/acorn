//! Hybrid fingerprint implementation that runs both old and new fingerprint
//! data structures and panics if they ever return different results.
//! This is used for validating correctness, not for speed.

use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

use crate::kernel::aliases::{Literal, Term};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::new_fingerprint::{NewFingerprintSpecializer, NewFingerprintUnifier};
use crate::kernel::old_fingerprint::{OldFingerprintSpecializer, OldFingerprintUnifier};

/// A hybrid fingerprint unifier that runs both old and new implementations
/// and panics if they return different results.
#[derive(Clone, Debug)]
pub struct HybridFingerprintUnifier<T: Clone + Debug + Eq + Hash> {
    old: OldFingerprintUnifier<T>,
    new: NewFingerprintUnifier<T>,
}

impl<T: Clone + Debug + Eq + Hash> HybridFingerprintUnifier<T> {
    pub fn new() -> HybridFingerprintUnifier<T> {
        HybridFingerprintUnifier {
            old: OldFingerprintUnifier::new(),
            new: NewFingerprintUnifier::new(),
        }
    }

    pub fn insert(
        &mut self,
        term: &Term,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        self.old
            .insert(term, value.clone(), local_context, kernel_context);
        self.new.insert(term, value, local_context, kernel_context);
    }

    /// Find all T with a fingerprint that this term could unify with.
    /// Panics if old and new implementations return different results.
    pub fn find_unifying(
        &self,
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<&T> {
        let old_results = self.old.find_unifying(term, local_context, kernel_context);
        let new_results = self.new.find_unifying(term, local_context, kernel_context);

        // Compare as sets since order may differ
        let old_set: HashSet<_> = old_results.iter().map(|v| *v).collect();
        let new_set: HashSet<_> = new_results.iter().map(|v| *v).collect();

        // Check for items in old but not in new (false negatives in new)
        for item in &old_set {
            if !new_set.contains(item) {
                panic!(
                    "HybridFingerprintUnifier: new implementation missing result {:?}\n\
                     term: {:?}\n\
                     old results: {:?}\n\
                     new results: {:?}",
                    item, term, old_results, new_results
                );
            }
        }

        // Check for items in new but not in old (false positives in new)
        for item in &new_set {
            if !old_set.contains(item) {
                panic!(
                    "HybridFingerprintUnifier: new implementation has extra result {:?}\n\
                     term: {:?}\n\
                     old results: {:?}\n\
                     new results: {:?}",
                    item, term, old_results, new_results
                );
            }
        }

        // Return the new results (they're the same)
        new_results
    }
}

/// A hybrid fingerprint specializer that runs both old and new implementations
/// and panics if they return different results.
#[derive(Clone)]
pub struct HybridFingerprintSpecializer<T: Clone + Debug + Eq + Hash> {
    old: OldFingerprintSpecializer<T>,
    new: NewFingerprintSpecializer<T>,
}

impl<T: Clone + Debug + Eq + Hash> HybridFingerprintSpecializer<T> {
    pub fn new() -> HybridFingerprintSpecializer<T> {
        HybridFingerprintSpecializer {
            old: OldFingerprintSpecializer::new(),
            new: NewFingerprintSpecializer::new(),
        }
    }

    pub fn insert(
        &mut self,
        literal: &Literal,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        self.old
            .insert(literal, value.clone(), local_context, kernel_context);
        self.new
            .insert(literal, value, local_context, kernel_context);
    }

    /// Find all ids with a fingerprint that this literal could specialize into.
    /// Only does a single left->right direction of lookup.
    /// Panics if old and new implementations return different results.
    pub fn find_specializing(
        &self,
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<&T> {
        let old_results = self
            .old
            .find_specializing(left, right, local_context, kernel_context);
        let new_results = self
            .new
            .find_specializing(left, right, local_context, kernel_context);

        // Compare as sets since order may differ
        let old_set: HashSet<_> = old_results.iter().map(|v| *v).collect();
        let new_set: HashSet<_> = new_results.iter().map(|v| *v).collect();

        // Check for items in old but not in new (false negatives in new)
        for item in &old_set {
            if !new_set.contains(item) {
                panic!(
                    "HybridFingerprintSpecializer: new implementation missing result {:?}\n\
                     left: {:?}\n\
                     right: {:?}\n\
                     old results: {:?}\n\
                     new results: {:?}",
                    item, left, right, old_results, new_results
                );
            }
        }

        // Check for items in new but not in old (false positives in new)
        for item in &new_set {
            if !old_set.contains(item) {
                panic!(
                    "HybridFingerprintSpecializer: new implementation has extra result {:?}\n\
                     left: {:?}\n\
                     right: {:?}\n\
                     old results: {:?}\n\
                     new results: {:?}",
                    item, left, right, old_results, new_results
                );
            }
        }

        // Return the new results (they're the same)
        new_results
    }
}
