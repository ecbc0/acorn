use std::collections::{BTreeMap, HashMap};

use crate::kernel::atom::Atom;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::PathStep;
use crate::kernel::term::Term;
use crate::kernel::types::GroundTypeId;

/// A coarse categorization of types for fingerprint indexing.
/// Ground types are distinguished by their ID, while all arrow types
/// are grouped together and all applied types are grouped together.
/// This is cheap to compare and hash while still providing useful discrimination.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum TypeCategory {
    /// A ground type, distinguished by ID
    Ground(GroundTypeId),

    /// An arrow/function type (any Pi type)
    Arrow,

    /// An applied type constructor (like List[T])
    Applied,
}

impl TypeCategory {
    /// Create a TypeCategory from a type Term.
    fn from_type_term(type_term: &Term) -> TypeCategory {
        if let Some(gid) = type_term.as_ref().as_type_atom() {
            TypeCategory::Ground(gid)
        } else if type_term.as_ref().is_pi() {
            TypeCategory::Arrow
        } else {
            TypeCategory::Applied
        }
    }
}

/// A fingerprint component describes the head of a term at a particular binary path.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum FingerprintComponent {
    /// The path goes through a variable - could match anything.
    Below,

    /// The path doesn't exist (term is smaller than path).
    Nothing,

    /// Found a subterm with this type category and head atom.
    /// Variable ids are all replaced with 0 for uniform storage.
    Something(TypeCategory, Atom),
}

impl FingerprintComponent {
    fn new(
        term: &Term,
        path: &[PathStep],
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> FingerprintComponent {
        match term.as_ref().get_term_at_path(path) {
            Some(subterm) => {
                let type_term = subterm.get_type_with_context(local_context, kernel_context);
                let type_category = TypeCategory::from_type_term(&type_term);

                match subterm.get_head_atom() {
                    Atom::Variable(_) => {
                        FingerprintComponent::Something(type_category, Atom::Variable(0))
                    }
                    atom => FingerprintComponent::Something(type_category, *atom),
                }
            }
            None => {
                // Path doesn't exist - check if we stopped at a variable
                // Need to traverse as far as we can and check
                let mut current = term.as_ref();
                for step in path {
                    if current.atomic_variable().is_some() {
                        return FingerprintComponent::Below;
                    }
                    match current.split_application() {
                        Some((func, arg)) => {
                            current = match step {
                                PathStep::Function => func,
                                PathStep::Argument => arg,
                            };
                        }
                        None => return FingerprintComponent::Nothing,
                    }
                }
                // Should not reach here since get_term_at_path returned None
                FingerprintComponent::Nothing
            }
        }
    }

    /// Whether a unification could combine paths with these fingerprint components.
    fn could_unify(&self, other: &FingerprintComponent) -> bool {
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

    /// Whether a specialization could turn the 'self' component into the 'other' component.
    /// For specialization: query (self) is more general, stored (other) is more specific.
    /// A query can specialize into a stored pattern if:
    /// - The query has a variable (can become anything via substitution)
    /// - Or both have the same concrete atom
    fn could_specialize(&self, other: &FingerprintComponent) -> bool {
        match (self, other) {
            (FingerprintComponent::Below, _) => true,
            (_, FingerprintComponent::Below) => false,
            (FingerprintComponent::Nothing, FingerprintComponent::Nothing) => true,
            (FingerprintComponent::Something(t1, a1), FingerprintComponent::Something(t2, a2)) => {
                if t1 != t2 {
                    return false;
                }
                // If the query (self) has a variable, it can be specialized to match anything
                if a1.is_variable() {
                    return true;
                }
                a1 == a2
            }
            _ => false,
        }
    }
}

/// Paths to sample for fingerprinting.
const PATHS: [&[PathStep]; 7] = [
    &[],                                       // root
    &[PathStep::Function],                     // function part
    &[PathStep::Argument],                     // argument part
    &[PathStep::Function, PathStep::Function], // function's function
    &[PathStep::Function, PathStep::Argument], // function's argument
    &[PathStep::Argument, PathStep::Function], // arg's function (if arg is application)
    &[PathStep::Argument, PathStep::Argument], // arg's argument
];

/// The fingerprints of a term at a selection of binary paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TermFingerprint {
    components: [FingerprintComponent; 7],
}

impl TermFingerprint {
    fn new(
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> TermFingerprint {
        let mut components = [FingerprintComponent::Nothing; 7];
        for (i, path) in PATHS.iter().enumerate() {
            components[i] = FingerprintComponent::new(term, path, local_context, kernel_context);
        }
        TermFingerprint { components }
    }

    fn could_unify(&self, other: &TermFingerprint) -> bool {
        for i in 0..PATHS.len() {
            if !self.components[i].could_unify(&other.components[i]) {
                return false;
            }
        }
        true
    }

    fn could_specialize(&self, other: &TermFingerprint) -> bool {
        for i in 0..PATHS.len() {
            if !self.components[i].could_specialize(&other.components[i]) {
                return false;
            }
        }
        true
    }
}

/// A data structure designed to quickly find which terms unify with a query term.
#[derive(Clone, Debug)]
pub struct FingerprintUnifier<T> {
    trees: HashMap<TypeCategory, BTreeMap<TermFingerprint, Vec<T>>>,
}

impl<T> FingerprintUnifier<T> {
    pub fn new() -> FingerprintUnifier<T> {
        FingerprintUnifier {
            trees: HashMap::new(),
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
        let type_term = term.get_type_with_context(local_context, kernel_context);
        let type_category = TypeCategory::from_type_term(&type_term);
        let tree = self.trees.entry(type_category).or_insert(BTreeMap::new());
        tree.entry(fingerprint).or_insert(vec![]).push(value);
    }

    /// Find all T with a fingerprint that this term could unify with.
    pub fn find_unifying(
        &self,
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<&T> {
        let fingerprint = TermFingerprint::new(term, local_context, kernel_context);
        let type_term = term.get_type_with_context(local_context, kernel_context);
        let type_category = TypeCategory::from_type_term(&type_term);

        let mut result = vec![];

        let tree = match self.trees.get(&type_category) {
            Some(tree) => tree,
            None => return result,
        };

        // At around 8000 goals in library, we tried doing smart tree things instead of
        // dumb search, but the dumb search was faster.
        for (f, values) in tree {
            if fingerprint.could_unify(f) {
                for v in values {
                    result.push(v);
                }
            }
        }

        result
    }
}

/// The fingerprints of a literal at a selection of binary paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct LiteralFingerprint {
    left: TermFingerprint,
    right: TermFingerprint,
}

impl LiteralFingerprint {
    fn new(
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

    fn could_specialize(&self, other: &LiteralFingerprint) -> bool {
        self.left.could_specialize(&other.left) && self.right.could_specialize(&other.right)
    }
}

/// A data structure designed to quickly find which literals are a specialization of a query literal.
#[derive(Clone)]
pub struct FingerprintSpecializer<T> {
    trees: HashMap<TypeCategory, BTreeMap<LiteralFingerprint, Vec<T>>>,
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
        let type_term = literal
            .left
            .get_type_with_context(local_context, kernel_context);
        let type_category = TypeCategory::from_type_term(&type_term);
        let tree = self.trees.entry(type_category).or_insert(BTreeMap::new());
        tree.entry(fingerprint).or_insert(vec![]).push(value);
    }

    /// Find all ids with a fingerprint that this literal could specialize into.
    /// Only does a single left->right direction of lookup.
    pub fn find_specializing(
        &self,
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<&T> {
        let fingerprint = LiteralFingerprint::new(left, right, local_context, kernel_context);
        let type_term = left.get_type_with_context(local_context, kernel_context);
        let type_category = TypeCategory::from_type_term(&type_term);

        let mut result = vec![];

        let tree = match self.trees.get(&type_category) {
            Some(tree) => tree,
            None => return result,
        };

        // At around 8000 goals in library, we tried doing smart tree things instead of
        // dumb search, but the dumb search was faster.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_application() {
        // m0: (Bool, Bool) -> Bool
        let term = Term::parse("m0(c0, c1)");
        let (func, arg) = term.as_ref().split_application().unwrap();

        // func should be m0(c0)
        assert_eq!(func.num_args(), 1);

        // arg should be c1
        assert!(arg.is_atomic());
    }

    #[test]
    fn test_path_navigation() {
        // m0: (Bool, Bool) -> Bool
        let term = Term::parse("m0(c0, c1)");

        // [] should return the whole term
        let root = term.as_ref().get_term_at_path(&[]).unwrap();
        assert_eq!(root.num_args(), 2);

        // [Argument] should return c1 (the last arg)
        let last_arg = term
            .as_ref()
            .get_term_at_path(&[PathStep::Argument])
            .unwrap();
        assert!(last_arg.is_atomic());

        // [Function] should return m0(c0)
        let func = term
            .as_ref()
            .get_term_at_path(&[PathStep::Function])
            .unwrap();
        assert_eq!(func.num_args(), 1);

        // [Function, Argument] should return c0
        let first_arg = term
            .as_ref()
            .get_term_at_path(&[PathStep::Function, PathStep::Argument])
            .unwrap();
        assert!(first_arg.is_atomic());

        // [Function, Function] should return m0 (the head)
        let head = term
            .as_ref()
            .get_term_at_path(&[PathStep::Function, PathStep::Function])
            .unwrap();
        assert!(head.is_atomic());
    }

    #[test]
    fn test_fingerprint() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("m0", "(Bool, Bool) -> Bool");
        let lctx = kctx.make_local(&["Bool", "Bool"]);

        // m0: (Bool, Bool) -> Bool, x0 and x1 are Bool
        let term = Term::parse("m0(x0, x1)");
        TermFingerprint::new(&term, &lctx, &kctx);
    }

    #[test]
    fn test_fingerprint_matching() {
        let mut kctx = KernelContext::new();
        // c0, c1 are Bool; c2 is (Bool, Bool) -> Bool
        kctx.add_constants(&["c0", "c1"], "Bool")
            .add_constant("c2", "(Bool, Bool) -> Bool");
        let lctx = kctx.make_local(&["Bool"]);

        let term1 = Term::parse("c2(x0, c0)");
        let term2 = Term::parse("c2(c1, c0)");
        assert!(TermFingerprint::new(&term1, &lctx, &kctx)
            .could_unify(&TermFingerprint::new(&term2, &lctx, &kctx)));
    }

    #[test]
    fn test_fingerprint_tree() {
        let mut kctx = KernelContext::new();
        // c0, c1 are Bool; c2 is (Bool, Bool) -> Bool
        kctx.add_constants(&["c0", "c1"], "Bool")
            .add_constant("c2", "(Bool, Bool) -> Bool");
        let lctx = kctx.make_local(&["Bool"]);

        let mut tree = FingerprintUnifier::new();
        let term1 = Term::parse("c2(x0, c0)");
        let term2 = Term::parse("c2(c1, c0)");
        tree.insert(&term1, 1, &lctx, &kctx);
        assert!(tree.find_unifying(&term1, &lctx, &kctx).len() > 0);
        assert!(tree.find_unifying(&term2, &lctx, &kctx).len() > 0);
    }
}
