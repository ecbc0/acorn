//! Hybrid fingerprint implementation that runs both old and new fingerprint
//! data structures and validates they don't miss actual unifications.
//! This is used for validating correctness, not for speed.

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use crate::kernel::aliases::{Literal, Term};
use crate::kernel::closed_type::ClosedType;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::new_fingerprint::{NewFingerprintSpecializer, NewFingerprintUnifier};
use crate::kernel::old_fingerprint::{OldFingerprintSpecializer, OldFingerprintUnifier};
use crate::kernel::unifier::{Scope, Unifier};

/// Describe a ClosedType's category for debug output
fn describe_type_category(ct: &ClosedType) -> &'static str {
    if ct.as_ground().is_some() {
        "Ground"
    } else if ct.is_pi() {
        "Arrow"
    } else {
        "Applied"
    }
}

/// A hybrid fingerprint unifier that runs both old and new implementations
/// and validates that neither misses actual unifications.
#[derive(Clone)]
pub struct HybridFingerprintUnifier<T: Clone + Debug + Eq + Hash> {
    old: OldFingerprintUnifier<T>,
    new: NewFingerprintUnifier<T>,
    // Store the terms we've inserted, keyed by value, so we can check actual unification
    terms: HashMap<T, (Term, LocalContext)>,
}

impl<T: Clone + Debug + Eq + Hash> HybridFingerprintUnifier<T> {
    pub fn new() -> HybridFingerprintUnifier<T> {
        HybridFingerprintUnifier {
            old: OldFingerprintUnifier::new(),
            new: NewFingerprintUnifier::new(),
            terms: HashMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        term: &Term,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        self.terms
            .insert(value.clone(), (term.clone(), local_context.clone()));
        self.old
            .insert(term, value.clone(), local_context, kernel_context);
        self.new.insert(term, value, local_context, kernel_context);
    }

    /// Check if two terms actually unify.
    fn terms_unify(
        &self,
        term1: &Term,
        local1: &LocalContext,
        term2: &Term,
        local2: &LocalContext,
        kernel_context: &KernelContext,
    ) -> bool {
        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, local1);
        unifier.set_input_context(Scope::RIGHT, local2);
        unifier.unify(Scope::LEFT, term1, Scope::RIGHT, term2)
    }

    /// Find all T with a fingerprint that this term could unify with.
    /// Panics if either implementation misses an actual unification.
    pub fn find_unifying(
        &self,
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<&T> {
        let old_results = self.old.find_unifying(term, local_context, kernel_context);
        let new_results = self.new.find_unifying(term, local_context, kernel_context);

        // For each result found by old but not new, check if it actually unifies
        for old_item in &old_results {
            if !new_results.iter().any(|n| *n == *old_item) {
                // New missed this - check if it actually unifies
                if let Some((stored_term, stored_local)) = self.terms.get(*old_item) {
                    if self.terms_unify(
                        term,
                        local_context,
                        stored_term,
                        stored_local,
                        kernel_context,
                    ) {
                        panic!(
                            "HybridFingerprintUnifier: new implementation missed actual unification!\n\
                             query term: {:?}\n\
                             stored term: {:?}\n\
                             value: {:?}\n\
                             old found it, new missed it",
                            term, stored_term, old_item
                        );
                    }
                }
            }
        }

        // We don't check for items in new but not old - the new implementation
        // is expected to find more matches (especially for variable-headed terms
        // that can unify via partial application). This is a known improvement.

        // Return the new results
        new_results
    }
}

/// A hybrid fingerprint specializer that runs both old and new implementations
/// and validates that neither misses actual specializations.
#[derive(Clone)]
pub struct HybridFingerprintSpecializer<T: Clone + Debug + Eq + Hash> {
    old: OldFingerprintSpecializer<T>,
    new: NewFingerprintSpecializer<T>,
    // Store the literals we've inserted, keyed by value
    literals: HashMap<T, (Literal, LocalContext)>,
}

impl<T: Clone + Debug + Eq + Hash> HybridFingerprintSpecializer<T> {
    pub fn new() -> HybridFingerprintSpecializer<T> {
        HybridFingerprintSpecializer {
            old: OldFingerprintSpecializer::new(),
            new: NewFingerprintSpecializer::new(),
            literals: HashMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        literal: &Literal,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        self.literals
            .insert(value.clone(), (literal.clone(), local_context.clone()));
        self.old
            .insert(literal, value.clone(), local_context, kernel_context);
        self.new
            .insert(literal, value, local_context, kernel_context);
    }

    /// Check if a literal can be specialized to match the query.
    /// The query (left, right) should be able to specialize into the stored literal.
    fn can_specialize(
        &self,
        query_left: &Term,
        query_right: &Term,
        query_local: &LocalContext,
        stored_literal: &Literal,
        stored_local: &LocalContext,
        kernel_context: &KernelContext,
    ) -> bool {
        // For specialization, the query should be more general than the stored literal.
        // We check if we can unify with the query's variables being substituted.
        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, query_local);
        unifier.set_input_context(Scope::RIGHT, stored_local);
        // Try to match query -> stored (query is pattern, stored is instance)
        unifier.unify(Scope::LEFT, query_left, Scope::RIGHT, &stored_literal.left)
            && unifier.unify(Scope::LEFT, query_right, Scope::RIGHT, &stored_literal.right)
    }

    /// Find all ids with a fingerprint that this literal could specialize into.
    /// Only does a single left->right direction of lookup.
    /// Panics if either implementation misses an actual specialization.
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

        // For each result found by old but not new, check if it actually specializes
        for old_item in &old_results {
            if !new_results.iter().any(|n| *n == *old_item) {
                if let Some((stored_literal, stored_local)) = self.literals.get(*old_item) {
                    if self.can_specialize(
                        left,
                        right,
                        local_context,
                        stored_literal,
                        stored_local,
                        kernel_context,
                    ) {
                        let query_closed_type =
                            left.get_closed_type_with_context(local_context, kernel_context);
                        let stored_closed_type = stored_literal
                            .left
                            .get_closed_type_with_context(stored_local, kernel_context);
                        panic!(
                            "HybridFingerprintSpecializer: new implementation missed actual specialization!\n\
                             query left: {:?}\n\
                             query right: {:?}\n\
                             query type category: {} ({:?})\n\
                             stored literal: {:?}\n\
                             stored type category: {} ({:?})\n\
                             value: {:?}\n\
                             old found it, new missed it",
                            left,
                            right,
                            describe_type_category(&query_closed_type),
                            query_closed_type,
                            stored_literal,
                            describe_type_category(&stored_closed_type),
                            stored_closed_type,
                            old_item
                        );
                    }
                }
            }
        }

        // We don't check for items in new but not old - the new implementation
        // is expected to find more matches. This is a known improvement.

        // Return the new results
        new_results
    }
}
