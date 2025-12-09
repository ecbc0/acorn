use std::collections::{BTreeMap, HashMap};

use crate::kernel::aliases::{Literal, Term};
use crate::kernel::atom::Atom;
use crate::kernel::closed_type::ClosedType;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::TermRef;
use crate::kernel::types::GroundTypeId;

/// A step in a binary path through a term.
/// Treats applications in curried form: f(a, b) becomes ((f a) b).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum BinaryStep {
    /// Go to the function part of an application
    Function,
    /// Go to the argument part of an application
    Argument,
}

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
    /// Create a TypeCategory from a ClosedType.
    fn from_closed_type(ct: &ClosedType) -> TypeCategory {
        if let Some(gid) = ct.as_ground() {
            TypeCategory::Ground(gid)
        } else if ct.is_pi() {
            TypeCategory::Arrow
        } else {
            TypeCategory::Applied
        }
    }
}

/// A fingerprint component describes the head of a term at a particular binary path.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum NewFingerprintComponent {
    /// The path goes through a variable - could match anything.
    Below,

    /// The path doesn't exist (term is smaller than path).
    Nothing,

    /// Found a subterm with this type category and head atom.
    /// Variable ids are all replaced with 0 for uniform storage.
    Something(TypeCategory, Atom),
}

/// Navigate to a subterm using a binary path.
/// Returns None if the path doesn't exist or we hit an atomic term.
fn get_term_at_binary_path<'a>(term: TermRef<'a>, path: &[BinaryStep]) -> Option<TermRef<'a>> {
    if path.is_empty() {
        return Some(term);
    }

    // Try to split the application
    let (func, arg) = term.split_application()?;

    match path[0] {
        BinaryStep::Argument => get_term_at_binary_path(arg, &path[1..]),
        BinaryStep::Function => get_term_at_binary_path(func, &path[1..]),
    }
}

impl NewFingerprintComponent {
    fn new(
        term: &Term,
        path: &[BinaryStep],
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> NewFingerprintComponent {
        match get_term_at_binary_path(term.as_ref(), path) {
            Some(subterm) => {
                let closed_type =
                    subterm.get_closed_type_with_context(local_context, kernel_context);
                let type_category = TypeCategory::from_closed_type(&closed_type);

                match subterm.get_head_atom() {
                    Atom::Variable(_) => {
                        NewFingerprintComponent::Something(type_category, Atom::Variable(0))
                    }
                    atom => NewFingerprintComponent::Something(type_category, *atom),
                }
            }
            None => {
                // Path doesn't exist - check if we stopped at a variable
                // Need to traverse as far as we can and check
                let mut current = term.as_ref();
                for step in path {
                    if current.atomic_variable().is_some() {
                        return NewFingerprintComponent::Below;
                    }
                    match current.split_application() {
                        Some((func, arg)) => {
                            current = match step {
                                BinaryStep::Function => func,
                                BinaryStep::Argument => arg,
                            };
                        }
                        None => return NewFingerprintComponent::Nothing,
                    }
                }
                // Should not reach here since get_term_at_binary_path returned None
                NewFingerprintComponent::Nothing
            }
        }
    }

    /// Whether a unification could combine paths with these fingerprint components.
    fn could_unify(&self, other: &NewFingerprintComponent) -> bool {
        match (self, other) {
            (NewFingerprintComponent::Below, _) => true,
            (_, NewFingerprintComponent::Below) => true,
            (NewFingerprintComponent::Nothing, NewFingerprintComponent::Nothing) => true,
            (
                NewFingerprintComponent::Something(t1, a1),
                NewFingerprintComponent::Something(t2, a2),
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

    /// Whether a specialization could turn the 'self' component into the 'other' component.
    /// For specialization: query (self) is more general, stored (other) is more specific.
    /// A query can specialize into a stored pattern if:
    /// - The query has a variable (can become anything via substitution)
    /// - Or both have the same concrete atom
    fn could_specialize(&self, other: &NewFingerprintComponent) -> bool {
        match (self, other) {
            (NewFingerprintComponent::Below, _) => true,
            (_, NewFingerprintComponent::Below) => false,
            (NewFingerprintComponent::Nothing, NewFingerprintComponent::Nothing) => true,
            (
                NewFingerprintComponent::Something(t1, a1),
                NewFingerprintComponent::Something(t2, a2),
            ) => {
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

/// Binary paths to sample for fingerprinting.
const BINARY_PATHS: [&[BinaryStep]; 7] = [
    &[],                                           // root
    &[BinaryStep::Function],                       // function part
    &[BinaryStep::Argument],                       // argument part
    &[BinaryStep::Function, BinaryStep::Function], // function's function
    &[BinaryStep::Function, BinaryStep::Argument], // function's argument
    &[BinaryStep::Argument, BinaryStep::Function], // arg's function (if arg is application)
    &[BinaryStep::Argument, BinaryStep::Argument], // arg's argument
];

/// The fingerprints of a term at a selection of binary paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NewTermFingerprint {
    components: [NewFingerprintComponent; 7],
}

impl NewTermFingerprint {
    fn new(
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> NewTermFingerprint {
        let mut components = [NewFingerprintComponent::Nothing; 7];
        for (i, path) in BINARY_PATHS.iter().enumerate() {
            components[i] = NewFingerprintComponent::new(term, path, local_context, kernel_context);
        }
        NewTermFingerprint { components }
    }

    fn could_unify(&self, other: &NewTermFingerprint) -> bool {
        for i in 0..BINARY_PATHS.len() {
            if !self.components[i].could_unify(&other.components[i]) {
                return false;
            }
        }
        true
    }

    fn could_specialize(&self, other: &NewTermFingerprint) -> bool {
        for i in 0..BINARY_PATHS.len() {
            if !self.components[i].could_specialize(&other.components[i]) {
                return false;
            }
        }
        true
    }
}

/// A data structure designed to quickly find which terms unify with a query term.
#[derive(Clone, Debug)]
pub struct NewFingerprintUnifier<T> {
    trees: HashMap<TypeCategory, BTreeMap<NewTermFingerprint, Vec<T>>>,
}

impl<T> NewFingerprintUnifier<T> {
    pub fn new() -> NewFingerprintUnifier<T> {
        NewFingerprintUnifier {
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
        let fingerprint = NewTermFingerprint::new(term, local_context, kernel_context);
        let closed_type = term.get_closed_type_with_context(local_context, kernel_context);
        let type_category = TypeCategory::from_closed_type(&closed_type);
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
        let fingerprint = NewTermFingerprint::new(term, local_context, kernel_context);
        let closed_type = term.get_closed_type_with_context(local_context, kernel_context);
        let type_category = TypeCategory::from_closed_type(&closed_type);

        let mut result = vec![];

        let tree = match self.trees.get(&type_category) {
            Some(tree) => tree,
            None => return result,
        };

        // TODO: do smart tree things instead of this dumb exhaustive search
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
struct NewLiteralFingerprint {
    left: NewTermFingerprint,
    right: NewTermFingerprint,
}

impl NewLiteralFingerprint {
    fn new(
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> NewLiteralFingerprint {
        NewLiteralFingerprint {
            left: NewTermFingerprint::new(left, local_context, kernel_context),
            right: NewTermFingerprint::new(right, local_context, kernel_context),
        }
    }

    fn could_specialize(&self, other: &NewLiteralFingerprint) -> bool {
        self.left.could_specialize(&other.left) && self.right.could_specialize(&other.right)
    }
}

/// A data structure designed to quickly find which literals are a specialization of a query literal.
#[derive(Clone)]
pub struct NewFingerprintSpecializer<T> {
    trees: HashMap<TypeCategory, BTreeMap<NewLiteralFingerprint, Vec<T>>>,
}

impl<T> NewFingerprintSpecializer<T> {
    pub fn new() -> NewFingerprintSpecializer<T> {
        NewFingerprintSpecializer {
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
        let fingerprint = NewLiteralFingerprint::new(
            &literal.left,
            &literal.right,
            local_context,
            kernel_context,
        );
        let closed_type = literal
            .left
            .get_closed_type_with_context(local_context, kernel_context);
        let type_category = TypeCategory::from_closed_type(&closed_type);
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
        let fingerprint = NewLiteralFingerprint::new(left, right, local_context, kernel_context);
        let closed_type = left.get_closed_type_with_context(local_context, kernel_context);
        let type_category = TypeCategory::from_closed_type(&closed_type);

        let mut result = vec![];

        let tree = match self.trees.get(&type_category) {
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

// Tests for new fingerprint matching.
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

    #[test]
    fn test_split_application() {
        let lctx = test_local_context();
        let kctx = test_kernel_context();
        // m0: (Bool, Bool) -> Bool
        let term = Term::parse_with_context("m0(c0, c1)", &lctx, &kctx);
        let (func, arg) = term.as_ref().split_application().unwrap();

        // func should be m0(c0)
        assert_eq!(func.num_args(), 1);

        // arg should be c1
        assert!(arg.is_atomic());
    }

    #[test]
    fn test_binary_path_navigation() {
        let lctx = test_local_context();
        let kctx = test_kernel_context();
        // m0: (Bool, Bool) -> Bool
        let term = Term::parse_with_context("m0(c0, c1)", &lctx, &kctx);

        // [] should return the whole term
        let root = get_term_at_binary_path(term.as_ref(), &[]).unwrap();
        assert_eq!(root.num_args(), 2);

        // [Argument] should return c1 (the last arg)
        let last_arg = get_term_at_binary_path(term.as_ref(), &[BinaryStep::Argument]).unwrap();
        assert!(last_arg.is_atomic());

        // [Function] should return m0(c0)
        let func = get_term_at_binary_path(term.as_ref(), &[BinaryStep::Function]).unwrap();
        assert_eq!(func.num_args(), 1);

        // [Function, Argument] should return c0
        let first_arg =
            get_term_at_binary_path(term.as_ref(), &[BinaryStep::Function, BinaryStep::Argument])
                .unwrap();
        assert!(first_arg.is_atomic());

        // [Function, Function] should return m0 (the head)
        let head =
            get_term_at_binary_path(term.as_ref(), &[BinaryStep::Function, BinaryStep::Function])
                .unwrap();
        assert!(head.is_atomic());
    }

    #[test]
    fn test_new_fingerprint() {
        let lctx = test_local_context();
        let kctx = test_kernel_context();
        // m0: (Bool, Bool) -> Bool, x0 and x1 are Bool
        let term = Term::parse_with_context("m0(x0, x1)", &lctx, &kctx);
        NewTermFingerprint::new(&term, &lctx, &kctx);
    }

    #[test]
    fn test_new_fingerprint_matching() {
        let lctx = test_local_context();
        let kctx = test_kernel_context();
        let term1 = Term::parse_with_context("m2(x0, c0)", &lctx, &kctx);
        let term2 = Term::parse_with_context("m2(c1, c0)", &lctx, &kctx);
        assert!(NewTermFingerprint::new(&term1, &lctx, &kctx)
            .could_unify(&NewTermFingerprint::new(&term2, &lctx, &kctx)));
    }

    #[test]
    fn test_new_fingerprint_tree() {
        let lctx = test_local_context();
        let kctx = test_kernel_context();
        let mut tree = NewFingerprintUnifier::new();
        let term1 = Term::parse_with_context("m2(x0, c0)", &lctx, &kctx);
        let term2 = Term::parse_with_context("m2(c1, c0)", &lctx, &kctx);
        tree.insert(&term1, 1, &lctx, &kctx);
        assert!(tree.find_unifying(&term1, &lctx, &kctx).len() > 0);
        assert!(tree.find_unifying(&term2, &lctx, &kctx).len() > 0);
    }
}
