use std::collections::{BTreeMap, HashMap};

use crate::kernel::aliases::{Literal, Term};
use crate::kernel::atom::Atom;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::types::TypeId;

// A fingerprint component describes the head of a term at a particular "path" from this term.
// The path is the sequence of arg indices to get to that term
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum OldFingerprintComponent {
    // The path to this term goes through a variable.
    Below,

    // The path to this term goes through a leaf node.
    Nothing,

    // The head of the subterm at this path.
    // Variable ids are all replaced with 0, because we want to store all variables the same way
    // in the fingerprint tree.
    Something(TypeId, Atom),
}

impl OldFingerprintComponent {
    fn new(
        term: &Term,
        path: &&[usize],
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> OldFingerprintComponent {
        // Use get_term_at_path to traverse to the subterm
        match term.get_term_at_path(*path) {
            Some(subterm) => match subterm.get_head_atom() {
                Atom::Variable(_) => OldFingerprintComponent::Something(
                    subterm.get_term_type_with_context(local_context, kernel_context),
                    Atom::Variable(0),
                ),
                a => OldFingerprintComponent::Something(
                    subterm.get_term_type_with_context(local_context, kernel_context),
                    *a,
                ),
            },
            None => {
                // Path doesn't exist - check if we stopped at a variable
                // Need to traverse as far as we can and check
                let mut current = term.clone();
                for &i in *path {
                    if current.atomic_variable().is_some() {
                        return OldFingerprintComponent::Below;
                    }
                    match current.get_term_at_path(&[i]) {
                        Some(next) => current = next.clone(),
                        None => return OldFingerprintComponent::Nothing,
                    }
                }
                // Should not reach here since get_term_at_path returned None
                OldFingerprintComponent::Nothing
            }
        }
    }

    // Whether a unification could combine paths with these fingerprint components
    fn could_unify(&self, other: &OldFingerprintComponent) -> bool {
        match (self, other) {
            (OldFingerprintComponent::Below, _) => true,
            (_, OldFingerprintComponent::Below) => true,
            (OldFingerprintComponent::Nothing, OldFingerprintComponent::Nothing) => true,
            (
                OldFingerprintComponent::Something(t1, a1),
                OldFingerprintComponent::Something(t2, a2),
            ) => {
                if t1 != t2 {
                    return false;
                }
                if a1.is_variable() || a2.is_variable() {
                    return true;
                }
                a1 == a2
            }
            _ => false,
        }
    }

    // Whether a specialization could turn the 'self' component into the 'other' component
    fn could_specialize(&self, other: &OldFingerprintComponent) -> bool {
        match (self, other) {
            (OldFingerprintComponent::Below, _) => true,
            (_, OldFingerprintComponent::Below) => false,
            (OldFingerprintComponent::Nothing, OldFingerprintComponent::Nothing) => true,
            (
                OldFingerprintComponent::Something(t1, a1),
                OldFingerprintComponent::Something(t2, a2),
            ) => {
                if t1 != t2 {
                    return false;
                }
                if a1.is_variable() {
                    return true;
                }
                a1 == a2
            }
            _ => false,
        }
    }
}

const PATHS: &[&[usize]] = &[&[], &[0], &[1], &[0, 0], &[0, 1], &[1, 0], &[1, 1]];

// The fingerprints of a term, at a selection of paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct OldTermFingerprint {
    components: [OldFingerprintComponent; PATHS.len()],
}

impl OldTermFingerprint {
    fn new(
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> OldTermFingerprint {
        let mut components = [OldFingerprintComponent::Nothing; PATHS.len()];
        for (i, path) in PATHS.iter().enumerate() {
            components[i] = OldFingerprintComponent::new(term, path, local_context, kernel_context);
        }
        OldTermFingerprint { components }
    }

    fn could_unify(&self, other: &OldTermFingerprint) -> bool {
        for i in 0..PATHS.len() {
            if !self.components[i].could_unify(&other.components[i]) {
                return false;
            }
        }
        true
    }

    fn could_specialize(&self, other: &OldTermFingerprint) -> bool {
        for i in 0..PATHS.len() {
            if !self.components[i].could_specialize(&other.components[i]) {
                return false;
            }
        }
        true
    }
}

// A data structure designed to quickly find which terms unify with a query term.
#[derive(Clone, Debug)]
pub struct OldFingerprintUnifier<T> {
    tree: BTreeMap<OldTermFingerprint, Vec<T>>,
}

impl<T> OldFingerprintUnifier<T> {
    pub fn new() -> OldFingerprintUnifier<T> {
        OldFingerprintUnifier {
            tree: BTreeMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        term: &Term,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        let fingerprint = OldTermFingerprint::new(term, local_context, kernel_context);
        self.tree.entry(fingerprint).or_insert(vec![]).push(value);
    }

    // Find all T with a fingerprint that this term could unify with.
    pub fn find_unifying(
        &self,
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<&T> {
        let fingerprint = OldTermFingerprint::new(term, local_context, kernel_context);
        let mut result = vec![];

        // TODO: do smart tree things instead of this dumb exhaustive search
        for (f, values) in &self.tree {
            if fingerprint.could_unify(f) {
                for v in values {
                    result.push(v);
                }
            }
        }

        result
    }
}

// The fingerprints of a literal, at a selection of paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct OldLiteralFingerprint {
    left: OldTermFingerprint,
    right: OldTermFingerprint,
}

impl OldLiteralFingerprint {
    fn new(
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> OldLiteralFingerprint {
        OldLiteralFingerprint {
            left: OldTermFingerprint::new(left, local_context, kernel_context),
            right: OldTermFingerprint::new(right, local_context, kernel_context),
        }
    }

    fn could_specialize(&self, other: &OldLiteralFingerprint) -> bool {
        self.left.could_specialize(&other.left) && self.right.could_specialize(&other.right)
    }
}

// A data structure designed to quickly find which literals are a specialization of a query literal.
// Identifies literals by a usize id.
#[derive(Clone)]
pub struct OldFingerprintSpecializer<T> {
    trees: HashMap<TypeId, BTreeMap<OldLiteralFingerprint, Vec<T>>>,
}

impl<T> OldFingerprintSpecializer<T> {
    pub fn new() -> OldFingerprintSpecializer<T> {
        OldFingerprintSpecializer {
            trees: HashMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        literal: &Literal,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        let fingerprint = OldLiteralFingerprint::new(
            &literal.left,
            &literal.right,
            local_context,
            kernel_context,
        );
        let tree = self
            .trees
            .entry(
                literal
                    .left
                    .get_term_type_with_context(local_context, kernel_context),
            )
            .or_insert(BTreeMap::new());
        tree.entry(fingerprint).or_insert(vec![]).push(value);
    }

    // Find all ids with a fingerprint that this literal could specialize into.
    // Only does a single left->right direction of lookup.
    pub fn find_specializing(
        &self,
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<&T> {
        let fingerprint = OldLiteralFingerprint::new(left, right, local_context, kernel_context);
        let mut result = vec![];

        let tree = match self
            .trees
            .get(&left.get_term_type_with_context(local_context, kernel_context))
        {
            Some(tree) => tree,
            None => return result,
        };

        // TODO: do smart tree things instead of this dumb exhaustive search
        for (f, values) in tree {
            if fingerprint.could_specialize(f) {
                for v in values {
                    result.push(v);
                }
            }
        }
        result
    }
}

// Tests for fingerprint matching.
// Using test_with_all_bool_types: c0-c9 are Bool; m0-m9 are (Bool, Bool) -> Bool.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::types::BOOL;

    fn test_local_context() -> LocalContext {
        LocalContext::new(vec![BOOL; 10])
    }

    fn test_kernel_context() -> KernelContext {
        KernelContext::test_with_all_bool_types()
    }

    fn make_fingerprint(
        term: &Term,
        lctx: &LocalContext,
        kctx: &KernelContext,
    ) -> OldTermFingerprint {
        OldTermFingerprint::new(term, lctx, kctx)
    }

    #[test]
    fn test_fingerprint() {
        let lctx = test_local_context();
        let kctx = test_kernel_context();
        // m0: (Bool, Bool) -> Bool, x0 and x1 are Bool
        let term = Term::parse_with_context("m0(x0, x1)", &lctx, &kctx);
        make_fingerprint(&term, &lctx, &kctx);
    }

    #[test]
    fn test_fingerprint_matching() {
        let lctx = test_local_context();
        let kctx = test_kernel_context();
        // m2: (Bool, Bool) -> Bool, m3: (Bool, Bool) -> Bool
        // term1: m2(x0, x1) where x0, x1 are Bool (2-arg function needs simplification)
        // Since m0-m9 are all (Bool, Bool) -> Bool, we simplify to 2-arg terms
        let term1 = Term::parse_with_context("m2(x0, c0)", &lctx, &kctx);
        let term2 = Term::parse_with_context("m2(c1, c0)", &lctx, &kctx);
        assert!(make_fingerprint(&term1, &lctx, &kctx)
            .could_unify(&make_fingerprint(&term2, &lctx, &kctx)));
    }

    #[test]
    fn test_fingerprint_tree() {
        let lctx = test_local_context();
        let kctx = test_kernel_context();
        let mut tree = OldFingerprintUnifier::new();
        // m2: (Bool, Bool) -> Bool
        let term1 = Term::parse_with_context("m2(x0, c0)", &lctx, &kctx);
        let term2 = Term::parse_with_context("m2(c1, c0)", &lctx, &kctx);
        tree.insert(&term1, 1, &lctx, &kctx);
        assert!(tree.find_unifying(&term1, &lctx, &kctx).len() > 0);
        assert!(tree.find_unifying(&term2, &lctx, &kctx).len() > 0);
    }
}
