use std::collections::{BTreeMap, HashMap};

use crate::kernel::aliases::{Literal, Term};
use crate::kernel::atom::Atom;
use crate::kernel::fat_term::TypeId;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;

// A fingerprint component describes the head of a term at a particular "path" from this term.
// The path is the sequence of arg indices to get to that term
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FingerprintComponent {
    // The path to this term goes through a variable.
    Below,

    // The path to this term goes through a leaf node.
    Nothing,

    // The head of the subterm at this path.
    // Variable ids are all replaced with 0, because we want to store all variables the same way
    // in the fingerprint tree.
    Something(TypeId, Atom),
}

impl FingerprintComponent {
    pub fn new(
        term: &Term,
        path: &&[usize],
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> FingerprintComponent {
        // Use get_term_at_path to traverse to the subterm
        match term.get_term_at_path(*path) {
            Some(subterm) => match subterm.get_head_atom() {
                Atom::Variable(_) => FingerprintComponent::Something(
                    subterm.get_term_type_with_context(local_context, kernel_context),
                    Atom::Variable(0),
                ),
                a => FingerprintComponent::Something(
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
                        return FingerprintComponent::Below;
                    }
                    match current.get_term_at_path(&[i]) {
                        Some(next) => current = next.clone(),
                        None => return FingerprintComponent::Nothing,
                    }
                }
                // Should not reach here since get_term_at_path returned None
                FingerprintComponent::Nothing
            }
        }
    }

    // Whether a unification could combine paths with these fingerprint components
    pub fn could_unify(&self, other: &FingerprintComponent) -> bool {
        match (self, other) {
            (FingerprintComponent::Below, _) => true,
            (_, FingerprintComponent::Below) => true,
            (FingerprintComponent::Nothing, FingerprintComponent::Nothing) => true,
            (FingerprintComponent::Something(t1, a1), FingerprintComponent::Something(t2, a2)) => {
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
    pub fn could_specialize(&self, other: &FingerprintComponent) -> bool {
        match (self, other) {
            (FingerprintComponent::Below, _) => true,
            (_, FingerprintComponent::Below) => false,
            (FingerprintComponent::Nothing, FingerprintComponent::Nothing) => true,
            (FingerprintComponent::Something(t1, a1), FingerprintComponent::Something(t2, a2)) => {
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
struct TermFingerprint {
    components: [FingerprintComponent; PATHS.len()],
}

impl TermFingerprint {
    pub fn new(
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> TermFingerprint {
        let mut components = [FingerprintComponent::Nothing; PATHS.len()];
        for (i, path) in PATHS.iter().enumerate() {
            components[i] = FingerprintComponent::new(term, path, local_context, kernel_context);
        }
        TermFingerprint { components }
    }

    pub fn could_unify(&self, other: &TermFingerprint) -> bool {
        for i in 0..PATHS.len() {
            if !self.components[i].could_unify(&other.components[i]) {
                return false;
            }
        }
        true
    }

    pub fn could_specialize(&self, other: &TermFingerprint) -> bool {
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
pub struct FingerprintUnifier<T> {
    tree: BTreeMap<TermFingerprint, Vec<T>>,
}

impl<T> FingerprintUnifier<T> {
    pub fn new() -> FingerprintUnifier<T> {
        FingerprintUnifier {
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
        let fingerprint = TermFingerprint::new(term, local_context, kernel_context);
        self.tree.entry(fingerprint).or_insert(vec![]).push(value);
    }

    // Find all T with a fingerprint that this term could unify with.
    pub fn find_unifying(
        &self,
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<&T> {
        let fingerprint = TermFingerprint::new(term, local_context, kernel_context);
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
struct LiteralFingerprint {
    left: TermFingerprint,
    right: TermFingerprint,
}

impl LiteralFingerprint {
    pub fn new(
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> LiteralFingerprint {
        LiteralFingerprint {
            left: TermFingerprint::new(left, local_context, kernel_context),
            right: TermFingerprint::new(right, local_context, kernel_context),
        }
    }

    pub fn could_specialize(&self, other: &LiteralFingerprint) -> bool {
        self.left.could_specialize(&other.left) && self.right.could_specialize(&other.right)
    }
}

// A data structure designed to quickly find which literals are a specialization of a query literal.
// Identifies literals by a usize id.
#[derive(Clone)]
pub struct FingerprintSpecializer<T> {
    trees: HashMap<TypeId, BTreeMap<LiteralFingerprint, Vec<T>>>,
}

impl<T> FingerprintSpecializer<T> {
    pub fn new() -> FingerprintSpecializer<T> {
        FingerprintSpecializer {
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
        let fingerprint =
            LiteralFingerprint::new(&literal.left, &literal.right, local_context, kernel_context);
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
        let fingerprint = LiteralFingerprint::new(left, right, local_context, kernel_context);
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

// These tests use Term::parse which creates EMPTY types.
// ThinTerm looks up types from the symbol table, so these tests only work with FatTerm.
#[cfg(all(test, not(feature = "thin")))]
mod tests {
    use super::*;

    fn test_local_context() -> LocalContext {
        LocalContext::with_types(vec![TypeId::new(1); 10])
    }

    fn make_fingerprint(term: &Term) -> TermFingerprint {
        let lctx = test_local_context();
        let kctx = KernelContext::test_with_constants(10, 10);
        TermFingerprint::new(term, &lctx, &kctx)
    }

    #[test]
    fn test_fingerprint() {
        let term = Term::parse("c0(x0, x1)");
        make_fingerprint(&term);
    }

    #[test]
    fn test_fingerprint_matching() {
        let term1 = Term::parse("c2(x0, x1, c0)");
        let term2 = Term::parse("c2(c1, c3(x0), c0)");
        assert!(make_fingerprint(&term1).could_unify(&make_fingerprint(&term2)));
    }

    #[test]
    fn test_fingerprint_tree() {
        let lctx = test_local_context();
        let kctx = KernelContext::test_with_constants(10, 10);
        let mut tree = FingerprintUnifier::new();
        let term1 = Term::parse("c2(x0, x1, c0)");
        let term2 = Term::parse("c2(c1, c3(x0), c0)");
        tree.insert(&term1, 1, &lctx, &kctx);
        assert!(tree.find_unifying(&term1, &lctx, &kctx).len() > 0);
        assert!(tree.find_unifying(&term2, &lctx, &kctx).len() > 0);
    }
}
