use std::cmp::Ordering;
use std::vec;

use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::pattern_tree::PatternTree;
use crate::kernel::term::{Decomposition, TermRef};

/// The GeneralizationSet stores general clauses in a way that allows us to quickly check whether
/// a new clause is a specialization of an existing one.
#[derive(Clone)]
pub struct GeneralizationSet {
    /// Stores an id for each clause.
    tree: PatternTree<usize>,
}

impl GeneralizationSet {
    pub fn new() -> GeneralizationSet {
        GeneralizationSet {
            tree: PatternTree::new(),
        }
    }

    /// Inserts a clause into the set, reordering it in every way that is KBO-nonincreasing.
    pub fn insert(&mut self, mut clause: Clause, id: usize, kernel_context: &KernelContext) {
        let mut generalized = vec![];
        all_generalized_forms(&mut clause, 0, &mut generalized, kernel_context);
        for c in generalized {
            self.tree.insert_clause(&c, id, kernel_context);
        }
    }

    pub fn find_generalization(
        &self,
        clause: Clause,
        kernel_context: &KernelContext,
    ) -> Option<usize> {
        let special = specialized_form(clause, kernel_context);
        if let Some(id) = self.tree.find_clause(&special, kernel_context) {
            return Some(*id);
        }
        None
    }
}

/// Compare two literals in a substitution-invariant way.
/// First compares left terms, then right terms if left terms are equal.
fn sub_invariant_literal_cmp(
    lit1: &Literal,
    lit2: &Literal,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Option<Ordering> {
    // First compare the left terms
    let left_cmp = sub_invariant_term_cmp(
        lit1.left.as_ref(),
        !lit1.positive,
        lit2.left.as_ref(),
        !lit2.positive,
        local_context,
        kernel_context,
    );
    match left_cmp {
        Some(Ordering::Equal) => {
            // If left terms are equal, compare right terms
            sub_invariant_term_cmp(
                lit1.right.as_ref(),
                !lit1.positive,
                lit2.right.as_ref(),
                !lit2.positive,
                local_context,
                kernel_context,
            )
        }
        other => other,
    }
}

/// Stable under variable substitution, like KBO, but hopefully closer to total in practice.
/// Specifically, if two terms are comparable, they must stay comparable under substitution.
/// If two terms are not comparable, anything goes under substitution.
///
/// Returns Greater if self > other.
/// Returns Less if other > self.
/// Returns None if they are not comparable.
/// Returns Equal if they are actually equal.
///
/// Concrete terms should always be orderable.
pub fn sub_invariant_term_cmp(
    left: TermRef,
    left_neg: bool,
    right: TermRef,
    right_neg: bool,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Option<Ordering> {
    // Compare the types, because these won't be changed by substitution.
    let type_cmp = left
        .get_type_with_context(local_context, kernel_context)
        .cmp(&right.get_type_with_context(local_context, kernel_context));
    if type_cmp != Ordering::Equal {
        return Some(type_cmp);
    }

    // Compare the signs
    let neg_cmp = left_neg.cmp(&right_neg);
    if neg_cmp != Ordering::Equal {
        return Some(neg_cmp);
    }

    // If either term is a variable, we can't compare them in a substitution-invariant way.
    if left.get_head_atom().is_variable() || right.get_head_atom().is_variable() {
        return None;
    }

    // Compare the term types.
    let type_cmp = left
        .get_type_with_context(local_context, kernel_context)
        .cmp(&right.get_type_with_context(local_context, kernel_context));
    if type_cmp != Ordering::Equal {
        return Some(type_cmp);
    }

    // Use decompose to recursively compare
    match (left.decompose(), right.decompose()) {
        (Decomposition::Atom(l_atom), Decomposition::Atom(r_atom)) => Some(l_atom.cmp(r_atom)),
        (Decomposition::Application(l_func, l_arg), Decomposition::Application(r_func, r_arg)) => {
            // Need to check for variables in function and argument parts
            // Since we already checked that top-level heads aren't variables,
            // but we still need to recurse properly
            match sub_invariant_term_cmp(
                l_func,
                false,
                r_func,
                false,
                local_context,
                kernel_context,
            ) {
                Some(Ordering::Equal) => sub_invariant_term_cmp(
                    l_arg,
                    false,
                    r_arg,
                    false,
                    local_context,
                    kernel_context,
                ),
                x => x,
            }
        }
        (Decomposition::Pi(l_input, l_output), Decomposition::Pi(r_input, r_output)) => {
            // Compare Pi types recursively
            match sub_invariant_term_cmp(
                l_input,
                false,
                r_input,
                false,
                local_context,
                kernel_context,
            ) {
                Some(Ordering::Equal) => sub_invariant_term_cmp(
                    l_output,
                    false,
                    r_output,
                    false,
                    local_context,
                    kernel_context,
                ),
                x => x,
            }
        }
        // Atom vs Application mismatch - shouldn't happen with equal heads and same num_args
        // But could happen with different structure, return based on which is simpler
        (Decomposition::Atom(_), Decomposition::Application(_, _)) => Some(Ordering::Less),
        (Decomposition::Application(_, _), Decomposition::Atom(_)) => Some(Ordering::Greater),
        // Pi vs other structures
        (Decomposition::Pi(_, _), _) => Some(Ordering::Less),
        (_, Decomposition::Pi(_, _)) => Some(Ordering::Greater),
    }
}

/// The generalized and specialized forms relate to each other.
/// When we specialize a clause and put it into the specialized form, it must match
/// one of the generalized forms.
/// The "form" includes both the order of the literals and the direction of each literal.
///
/// Call with zero to start the recursion. First we check all directions of the literals.
/// The start index is the first one to consider swapping.
fn all_generalized_forms(
    base_clause: &mut Clause,
    start_index: usize,
    output: &mut Vec<Clause>,
    kernel_context: &KernelContext,
) {
    if start_index >= base_clause.literals.len() {
        // We have a complete clause, so we can move on to the reordering stage.
        all_generalized_orders(base_clause, output, kernel_context);
        return;
    }
    let literal = &base_clause.literals[start_index];
    let local_context = base_clause.get_local_context();
    // Ignore literal sign in this stage
    let cmp = sub_invariant_term_cmp(
        literal.left.as_ref(),
        true,
        literal.right.as_ref(),
        true,
        local_context,
        kernel_context,
    );
    if cmp != Some(Ordering::Less) {
        // The pre-existing direction is okay.
        all_generalized_forms(base_clause, start_index + 1, output, kernel_context);
    }
    if cmp == None || cmp == Some(Ordering::Less) {
        // The swapped direction is okay.
        base_clause.literals[start_index].flip();
        all_generalized_forms(base_clause, start_index + 1, output, kernel_context);
        base_clause.literals[start_index].flip();
    }
}

/// Generate all orders of the provided clause that are a valid generalized form.
fn all_generalized_orders(
    base_clause: &Clause,
    output: &mut Vec<Clause>,
    kernel_context: &KernelContext,
) {
    let local_context = base_clause.get_local_context();

    // Helper function to generate all permutations recursively
    fn generate_permutations(
        literals: &[Literal],
        current: &mut Vec<Literal>,
        used: &mut Vec<bool>,
        output: &mut Vec<Clause>,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        // Base case: we've built a complete permutation
        if current.len() == literals.len() {
            let mut clause = Clause::from_literals_unnormalized(current.clone(), local_context);
            clause.normalize_var_ids_no_flip();
            output.push(clause);
            return;
        }

        // Try each unused literal as the next element
        for i in 0..literals.len() {
            if used[i] {
                continue;
            }

            // Check if this literal can be the next one in a non-increasing order
            if let Some(last) = current.last() {
                let cmp =
                    sub_invariant_literal_cmp(last, &literals[i], local_context, kernel_context);
                if cmp == Some(Ordering::Less) {
                    continue;
                }
            }

            // Mark this literal as used
            used[i] = true;
            current.push(literals[i].clone());

            // Recurse
            generate_permutations(
                literals,
                current,
                used,
                output,
                local_context,
                kernel_context,
            );

            // Backtrack
            current.pop();
            used[i] = false;
        }
    }

    let mut current = Vec::new();
    let mut used = vec![false; base_clause.literals.len()];
    generate_permutations(
        &base_clause.literals,
        &mut current,
        &mut used,
        output,
        local_context,
        kernel_context,
    );
}

/// Put this clause into the "specialized" form.
/// This should only be called on concrete clauses.
fn specialized_form(mut clause: Clause, kernel_context: &KernelContext) -> Clause {
    let local_context = clause.get_local_context().clone();

    // First, ensure each literal has the larger term on the left
    for literal in &mut clause.literals {
        let cmp = sub_invariant_term_cmp(
            literal.left.as_ref(),
            true,
            literal.right.as_ref(),
            true,
            &local_context,
            kernel_context,
        )
        .expect("Concrete terms should always be comparable");
        if cmp == Ordering::Less {
            // The right term is larger, so swap
            literal.flip();
        }
    }

    // Then, sort the literals using our comparison function
    // Since this is for concrete clauses, we can unwrap the comparison
    clause.literals.sort_by(|a, b| {
        sub_invariant_literal_cmp(a, b, &local_context, kernel_context)
            .expect("Concrete literals should always be comparable")
            .reverse() // Reverse to get non-increasing order
    });

    clause.normalize_var_ids_no_flip();
    clause
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clause_set_basic_generalization() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "(Bool, Bool) -> Bool")
            .add_constant("c1", "Bool -> Bool")
            .add_constants(&["c2", "c3", "c4", "c5", "c6", "c7", "c8", "c9"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert a general clause: c0(x0, c5) or c1(x0)
        let general_clause = kctx.make_clause("c0(x0, c5) or c1(x0)", &["Bool"]);
        clause_set.insert(general_clause, 1, &kctx);

        // Test that a specialized version is recognized (x0 -> c6)
        let special_clause = kctx.make_clause("c1(c6) or c0(c6, c5)", &[]);
        let result = clause_set.find_generalization(special_clause, &kctx);
        assert_eq!(result, Some(1), "Should find the generalization");
    }

    #[test]
    fn test_clause_set_reordered_literals() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "(Bool, Bool) -> Bool")
            .add_constant("c1", "Bool -> Bool")
            .add_constants(&["c2", "c3", "c4", "c5", "c6", "c7", "c8", "c9"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: c1(x0) or c0(x0, c5)
        let clause = kctx.make_clause("c1(x0) or c0(x0, c5)", &["Bool"]);
        clause_set.insert(clause, 2, &kctx);

        // Test that reordered specializations are recognized (x0 -> c6)
        let special1 = kctx.make_clause("c0(c6, c5) or c1(c6)", &[]);
        assert_eq!(clause_set.find_generalization(special1, &kctx), Some(2));

        // Another reordering (x0 -> c7)
        let special2 = kctx.make_clause("c1(c7) or c0(c7, c5)", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(2));
    }

    #[test]
    fn test_clause_set_flipped_equality() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("c1", "Bool -> Bool")
            .add_constants(&["c5", "c6", "c7"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: x0 = c5 or c1(x0)
        let clause = kctx.make_clause("x0 = c5 or c1(x0)", &["Bool"]);
        clause_set.insert(clause, 3, &kctx);

        // Test that flipped equalities are recognized (x0 -> c6)
        let special = kctx.make_clause("c6 = c5 or c1(c6)", &[]);
        assert_eq!(clause_set.find_generalization(special, &kctx), Some(3));

        // Also test with the equality already flipped (x0 -> c7)
        let special2 = kctx.make_clause("c5 = c7 or c1(c7)", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(3));
    }

    #[test]
    fn test_clause_set_no_generalization() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "(Bool, Bool) -> Bool")
            .add_constant("c1", "Bool -> Bool")
            .add_constants(&["c2", "c3", "c4", "c5", "c6", "c7", "c8", "c9"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert a specific clause: c0(c5, c6) or c1(c7)
        let clause = kctx.make_clause("c0(c5, c6) or c1(c7)", &[]);
        clause_set.insert(clause, 4, &kctx);

        // Test clauses that should NOT have generalizations
        let no_match1 = kctx.make_clause("c0(c5, c7) or c1(c7)", &[]);
        assert_eq!(clause_set.find_generalization(no_match1, &kctx), None);

        let no_match2 = kctx.make_clause("c0(c6, c5) or c1(c7)", &[]);
        assert_eq!(clause_set.find_generalization(no_match2, &kctx), None);
    }

    #[test]
    fn test_clause_set_multiple_variables() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "(Bool, Bool) -> Bool")
            .add_constants(&["c5", "c6", "c7", "c8"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: c0(x0, x1) or c0(x1, x0)
        let clause = kctx.make_clause("c0(x0, x1) or c0(x1, x0)", &["Bool", "Bool"]);
        clause_set.insert(clause, 5, &kctx);

        // Test various specializations (x0 -> c5, x1 -> c6)
        let special1 = kctx.make_clause("c0(c5, c6) or c0(c6, c5)", &[]);
        assert_eq!(clause_set.find_generalization(special1, &kctx), Some(5));

        // Reordered (x0 -> c7, x1 -> c8)
        let special2 = kctx.make_clause("c0(c8, c7) or c0(c7, c8)", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(5));

        // This should NOT match because the variable pattern is different
        let no_match = kctx.make_clause("c0(c5, c6) or c0(c7, c8)", &[]);
        assert_eq!(clause_set.find_generalization(no_match, &kctx), None);
    }

    #[test]
    fn test_clause_set_single_literal() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "(Bool, Bool) -> Bool")
            .add_constants(&["c5", "c6"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert single literal clauses
        let clause1 = kctx.make_clause("c0(x0, c5)", &["Bool"]);
        clause_set.insert(clause1, 6, &kctx);

        let clause2 = kctx.make_clause("x0 = c5", &["Bool"]);
        clause_set.insert(clause2, 7, &kctx);

        // Test specializations
        assert_eq!(
            clause_set.find_generalization(kctx.make_clause("c0(c6, c5)", &[]), &kctx),
            Some(6)
        );
        assert_eq!(
            clause_set.find_generalization(kctx.make_clause("c6 = c5", &[]), &kctx),
            Some(7)
        );
        assert_eq!(
            clause_set.find_generalization(kctx.make_clause("c5 = c6", &[]), &kctx),
            Some(7)
        );
    }

    #[test]
    fn test_clause_set_negated_literals() {
        let mut kctx = KernelContext::new();
        kctx.add_constants(&["c5", "c6", "c7", "c8"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: c5 = x0 or x1 != c6
        let clause = kctx.make_clause("c5 = x0 or x1 != c6", &["Bool", "Bool"]);
        clause_set.insert(clause, 1, &kctx);

        // Test that it matches correct specializations
        let special1 = kctx.make_clause("c5 = c7 or c8 != c6", &[]);
        assert_eq!(clause_set.find_generalization(special1, &kctx), Some(1));

        let special2 = kctx.make_clause("c7 != c6 or c5 = c7", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(1));

        let special3 = kctx.make_clause("c5 = c8 or c6 != c8", &[]);
        assert_eq!(clause_set.find_generalization(special3, &kctx), Some(1));
    }

    #[test]
    fn test_clause_set_no_positive_negative_confusion() {
        let mut kctx = KernelContext::new();
        kctx.add_constants(&["c5", "c6", "c7", "c8"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert a clause with a positive literal
        let positive_clause = kctx.make_clause("x0 = c5", &["Bool"]);
        clause_set.insert(positive_clause, 1, &kctx);

        // Insert a clause with a negative literal
        let negative_clause = kctx.make_clause("x0 != c6", &["Bool"]);
        clause_set.insert(negative_clause, 2, &kctx);

        // Test that positive matches positive
        assert_eq!(
            clause_set.find_generalization(kctx.make_clause("c7 = c5", &[]), &kctx),
            Some(1)
        );

        // Test that negative matches negative
        assert_eq!(
            clause_set.find_generalization(kctx.make_clause("c8 != c6", &[]), &kctx),
            Some(2)
        );

        // Test that positive does NOT match negative
        assert_eq!(
            clause_set.find_generalization(kctx.make_clause("c7 != c5", &[]), &kctx),
            None
        );

        // Test that negative does NOT match positive
        assert_eq!(
            clause_set.find_generalization(kctx.make_clause("c8 = c6", &[]), &kctx),
            None
        );
    }

    #[test]
    fn test_clause_set_mixed_positive_negative() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "(Bool, Bool) -> Bool")
            .add_constant("c1", "Bool -> Bool")
            .add_constants(&["c2", "c3", "c4", "c5", "c6", "c7", "c8", "c9"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: not c1(x0) or c0(x0, x1) or x1 != c5
        let clause = kctx.make_clause("not c1(x0) or c0(x0, x1) or x1 != c5", &["Bool", "Bool"]);
        clause_set.insert(clause, 1, &kctx);

        // Test various specializations
        let special1 = kctx.make_clause("not c1(c6) or c0(c6, c7) or c7 != c5", &[]);
        assert_eq!(clause_set.find_generalization(special1, &kctx), Some(1));

        let special2 = kctx.make_clause("c0(c8, c9) or c9 != c5 or not c1(c8)", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(1));

        // Test that wrong signs don't match
        let wrong1 = kctx.make_clause("c1(c6) or c0(c6, c7) or c7 != c5", &[]);
        assert_eq!(clause_set.find_generalization(wrong1, &kctx), None);

        let wrong2 = kctx.make_clause("not c1(c6) or not c0(c6, c7) or c7 != c5", &[]);
        assert_eq!(clause_set.find_generalization(wrong2, &kctx), None);
    }

    #[test]
    fn test_clause_set_all_negative() {
        let mut kctx = KernelContext::new();
        kctx.add_constants(&["c5", "c6", "c7", "c8"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: x0 != c5 or x1 != c6 or x0 != x1
        let clause = kctx.make_clause("x0 != c5 or x1 != c6 or x0 != x1", &["Bool", "Bool"]);
        clause_set.insert(clause, 1, &kctx);

        let special = kctx.make_clause("c7 != c5 or c8 != c6 or c7 != c8", &[]);
        assert_eq!(clause_set.find_generalization(special, &kctx), Some(1));

        let special2 = kctx.make_clause("c7 != c8 or c7 != c5 or c8 != c6", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(1));
    }

    #[test]
    fn test_clause_set_boolean_negation() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "(Bool, Bool) -> Bool")
            .add_constant("c1", "Bool -> Bool")
            .add_constants(&["c5", "c6", "c7"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: not c0(x0, c5) or c1(x0)
        let clause = kctx.make_clause("not c0(x0, c5) or c1(x0)", &["Bool"]);
        clause_set.insert(clause, 1, &kctx);

        let special = kctx.make_clause("not c0(c6, c5) or c1(c6)", &[]);
        assert_eq!(clause_set.find_generalization(special, &kctx), Some(1));

        let special2 = kctx.make_clause("c1(c7) or not c0(c7, c5)", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(1));

        // Test that signs matter
        let wrong = kctx.make_clause("c0(c6, c5) or c1(c6)", &[]);
        assert_eq!(clause_set.find_generalization(wrong, &kctx), None);
    }

    #[test]
    fn test_clause_set_compound_generalization() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "(Bool, Bool) -> Bool")
            .add_constants(&["c5", "c6", "c7"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: c0(c5, x0) = x0
        let general = kctx.make_clause("c0(c5, x0) = x0", &["Bool"]);
        clause_set.insert(general, 1, &kctx);

        // Specialization: c0(c5, c0(c6, c7)) = c0(c6, c7)
        let special = kctx.make_clause("c0(c5, c0(c6, c7)) = c0(c6, c7)", &[]);
        assert_eq!(clause_set.find_generalization(special, &kctx), Some(1));
    }

    #[test]
    fn test_clause_set_with_applied_variable() {
        // Test GeneralizationSet with applied variables (variables in function position).
        // Pattern: not x0(c5) or x0(x1) where x0: Bool -> Bool, x1: Bool
        // Query: not c1(c5) or c1(c6) where c1: Bool -> Bool
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "Bool") // placeholder
            .add_constant("c1", "Bool -> Bool")
            .add_constants(&["c2", "c3", "c4", "c5", "c6"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // x0: Bool -> Bool, x1: Bool
        let pattern = kctx.make_clause("not x0(c5) or x0(x1)", &["Bool -> Bool", "Bool"]);
        clause_set.insert(pattern, 42, &kctx);

        let query = kctx.make_clause("not c1(c5) or c1(c6)", &[]);
        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(found, Some(42), "Should match clause with applied variable");
    }

    #[test]
    fn test_clause_set_with_higher_order_function() {
        // Test with higher-order function type (Bool -> Bool, Bool) -> Bool
        // Pattern: not f(x0, x1) or x0(x1) where f: (Bool -> Bool, Bool) -> Bool
        // Query: not f(c1, c5) or c1(c5)
        let mut kctx = KernelContext::new();
        // c0: (Bool -> Bool, Bool) -> Bool (higher order function)
        kctx.add_constant("c0", "(Bool -> Bool, Bool) -> Bool")
            .add_constant("c1", "Bool -> Bool")
            .add_constants(&["c2", "c3", "c4", "c5", "c6"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // x0: Bool -> Bool, x1: Bool
        let pattern = kctx.make_clause("not c0(x0, x1) or x0(x1)", &["Bool -> Bool", "Bool"]);
        clause_set.insert(pattern, 42, &kctx);

        let query = kctx.make_clause("not c0(c1, c5) or c1(c5)", &[]);
        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(
            found,
            Some(42),
            "Should match pattern with higher-order function"
        );
    }

    #[test]
    fn test_clause_set_rejects_sign_mismatch() {
        // Test that signs are properly checked
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "(Bool -> Bool, Bool) -> Bool")
            .add_constant("c1", "Bool -> Bool")
            .add_constant("c5", "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert pattern with POSITIVE first literal, x0: Bool -> Bool, x1: Bool
        let pattern = kctx.make_clause("c0(x0, x1) or x0(x1)", &["Bool -> Bool", "Bool"]);
        clause_set.insert(pattern, 42, &kctx);

        // Query with NEGATIVE first literal
        let query = kctx.make_clause("not c0(c1, c5) or c1(c5)", &[]);
        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(found, None, "Should NOT match when signs are different");
    }

    /// This test is inspired by a failing case in no_mono_symbols mode.
    /// The pattern has a variable f: (Bool, Bool) -> Bool that gets applied to
    /// s(f) twice (where s: ((Bool, Bool) -> Bool) -> Bool), like f(s(f), s(f)).
    ///
    /// The query substitutes f with a curried application g(a) where:
    /// - g: A -> (Bool, Bool) -> Bool
    /// - a: A (some constant type)
    ///
    /// This tests that the pattern tree correctly matches:
    ///   pattern: f(s(f), s(f)) or r(f)
    ///   query:   g(a)(s(g(a)), s(g(a))) or r(g(a))
    ///
    /// Both are curried in term representation, so:
    ///   pattern: (f(s(f)))(s(f)) or r(f)
    ///   query:   ((g(a))(s(g(a))))(s(g(a))) or r(g(a))
    #[test]
    fn test_clause_set_curried_function_substitution() {
        use crate::kernel::atom::Atom;
        use crate::kernel::symbol::Symbol;
        use crate::kernel::term::Term;

        let mut kctx = KernelContext::new();
        // A is a constant type to simulate a type parameter
        kctx.add_datatype("A")
            // g0 takes A and returns a binary Bool function (like lte_from with type param)
            .add_constant("g0", "A -> (Bool, Bool) -> Bool")
            // s0 is a selector: given a binary function, returns a Bool (like Synthetic)
            .add_constant("s0", "((Bool, Bool) -> Bool) -> Bool")
            // c0 is a predicate on binary functions (like is_reflexive)
            .add_constant("c0", "((Bool, Bool) -> Bool) -> Bool")
            // c1 is a constant of type A (like the type argument)
            .add_constant("c1", "A");

        let mut clause_set = GeneralizationSet::new();

        // Pattern: not f(s0(f), s0(f)) or c0(f)
        // where f: (Bool, Bool) -> Bool (variable x0)
        let pattern = kctx.make_clause(
            "not x0(s0(x0), s0(x0)) or c0(x0)",
            &["(Bool, Bool) -> Bool"],
        );
        clause_set.insert(pattern.clone(), 99, &kctx);
        eprintln!("Inserted pattern: {:?}", pattern);

        // Build query manually: not g0(c1)(s0(g0(c1)), s0(g0(c1))) or c0(g0(c1))
        // Symbols: g0 = GlobalConstant(0), s0 = Synthetic(0), c0 = ScopedConstant(0), c1 = ScopedConstant(1)
        let g0_atom = Atom::Symbol(Symbol::GlobalConstant(0));
        let s0_atom = Atom::Symbol(Symbol::Synthetic(0));
        let c0_atom = Atom::Symbol(Symbol::ScopedConstant(0));
        let c1_atom = Atom::Symbol(Symbol::ScopedConstant(1));
        let c1_term = Term::atom(c1_atom);

        // g0(c1) - a function (Bool, Bool) -> Bool
        let g0_c1 = Term::new(g0_atom, vec![c1_term.clone()]);

        // s0(g0(c1)) - a Bool
        let s0_g0_c1 = Term::new(s0_atom, vec![g0_c1.clone()]);

        // g0(c1)(s0(g0(c1)), s0(g0(c1))) = g0(c1, s0(g0(c1)), s0(g0(c1))) in curried form
        // This is g0 applied to c1, then to s0(g0(c1)), then to s0(g0(c1))
        let g0_c1_s0_s0 = Term::new(
            g0_atom,
            vec![c1_term.clone(), s0_g0_c1.clone(), s0_g0_c1.clone()],
        );

        // c0(g0(c1))
        let c0_g0_c1 = Term::new(c0_atom, vec![g0_c1.clone()]);

        // Build the literals:
        // Literal 1: not g0(c1, s0(g0(c1)), s0(g0(c1))) = true
        let lit1 = Literal {
            positive: false,
            left: g0_c1_s0_s0,
            right: Term::new_true(),
        };

        // Literal 2: c0(g0(c1)) = true
        let lit2 = Literal {
            positive: true,
            left: c0_g0_c1,
            right: Term::new_true(),
        };

        let query = Clause::from_literals_unnormalized(vec![lit1, lit2], &LocalContext::empty());
        eprintln!("Query: {:?}", query);

        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(
            found,
            Some(99),
            "Should match pattern when f is substituted with curried application g0(c1)"
        );
    }

    /// Similar to the above test, but now the function takes TWO curried applications
    /// before becoming a binary function. This more closely matches the no_mono_symbols
    /// case where lte_from(Type)(lt) has two applications.
    ///
    /// Pattern: not f(s0(f), s0(f)) or c0(f)
    /// Query: not g0(Type)(c1)(s0(g0(Type)(c1)), s0(g0(Type)(c1))) or c0(g0(Type)(c1))
    ///
    /// Where Type is an actual Type symbol (like in no_mono_symbols mode).
    #[test]
    #[cfg(feature = "no_mono_symbols")]
    fn test_clause_set_with_type_symbol_argument() {
        use crate::kernel::atom::Atom;
        use crate::kernel::symbol::Symbol;
        use crate::kernel::term::Term;
        use crate::kernel::types::GroundTypeId;

        let mut kctx = KernelContext::new();
        // T is a type (like a type parameter bound in the environment)
        kctx.add_datatype("T")
            // g0 takes a Type, then another arg of that type, and returns (T, T) -> Bool
            // This simulates: forall T. A -> (T, T) -> Bool
            .add_constant("g0", "T -> T -> (T, T) -> Bool")
            // s0 is a selector: given a binary function, returns a T
            .add_constant("s0", "((T, T) -> Bool) -> T")
            // c0 is a predicate on binary functions (like is_reflexive)
            .add_constant("c0", "((T, T) -> Bool) -> Bool")
            // c1 is a constant of type T
            .add_constant("c1", "T");

        let mut clause_set = GeneralizationSet::new();

        // Pattern: not f(s0(f), s0(f)) or c0(f)
        // where f: (T, T) -> Bool (variable x0)
        let pattern = kctx.make_clause("not x0(s0(x0), s0(x0)) or c0(x0)", &["(T, T) -> Bool"]);
        clause_set.insert(pattern.clone(), 99, &kctx);
        eprintln!("Inserted pattern: {:?}", pattern);

        // Build query: not g0(Type)(c1)(s0(...), s0(...)) or c0(g0(Type)(c1))
        // g0 = GlobalConstant(0), s0 = Synthetic(0), c0 = ScopedConstant(0), c1 = ScopedConstant(1)
        // Type = Type(GroundTypeId(0)) which is the type T
        let g0_atom = Atom::Symbol(Symbol::GlobalConstant(0));
        let s0_atom = Atom::Symbol(Symbol::Synthetic(0));
        let c0_atom = Atom::Symbol(Symbol::ScopedConstant(0));
        let c1_atom = Atom::Symbol(Symbol::ScopedConstant(1));
        let type_atom = Atom::Symbol(Symbol::Type(GroundTypeId::new(0))); // T as a type symbol

        let type_term = Term::atom(type_atom);
        let c1_term = Term::atom(c1_atom);

        // g0(Type)(c1) = g0(Type, c1) - a function (T, T) -> Bool
        // This mirrors lte_from(Type)(lt) in no_mono_symbols mode
        let g0_type_c1 = Term::new(g0_atom, vec![type_term.clone(), c1_term.clone()]);

        // s0(g0(Type)(c1)) - a T
        let s0_g0_type_c1 = Term::new(s0_atom, vec![g0_type_c1.clone()]);

        // g0(Type)(c1)(s0(...), s0(...)) = g0(Type, c1, s0(...), s0(...))
        let g0_type_c1_s0_s0 = Term::new(
            g0_atom,
            vec![
                type_term.clone(),
                c1_term.clone(),
                s0_g0_type_c1.clone(),
                s0_g0_type_c1.clone(),
            ],
        );

        // c0(g0(Type)(c1))
        let c0_g0_type_c1 = Term::new(c0_atom, vec![g0_type_c1.clone()]);

        // Build the literals:
        let lit1 = Literal {
            positive: false,
            left: g0_type_c1_s0_s0,
            right: Term::new_true(),
        };

        let lit2 = Literal {
            positive: true,
            left: c0_g0_type_c1,
            right: Term::new_true(),
        };

        let query = Clause::from_literals_unnormalized(vec![lit1, lit2], &LocalContext::empty());
        eprintln!("Query: {:?}", query);

        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(
            found,
            Some(99),
            "Should match pattern when f is substituted with g0(Type)(c1)"
        );
    }

    /// This test exactly matches the failing scenario in no_mono_symbols mode:
    /// - The predicate (is_reflexive) takes a Type argument as well
    /// - Pattern: not f(s0(f), s0(f)) or g1(Type)(f)
    /// - Query: not g0(Type)(c1)(s0(...), s0(...)) or g1(Type)(g0(Type)(c1))
    #[test]
    #[cfg(feature = "no_mono_symbols")]
    fn test_clause_set_predicate_with_type_arg() {
        use crate::kernel::atom::Atom;
        use crate::kernel::symbol::Symbol;
        use crate::kernel::term::Term;
        use crate::kernel::types::GroundTypeId;

        let mut kctx = KernelContext::new();
        // T is a type (like a type parameter bound in the environment)
        kctx.add_datatype("T")
            // g0 (lte_from): Type -> T -> (T, T) -> Bool
            .add_constant("g0", "T -> T -> (T, T) -> Bool")
            // g1 (is_reflexive): Type -> ((T, T) -> Bool) -> Bool
            .add_constant("g1", "T -> ((T, T) -> Bool) -> Bool")
            // s0: ((T, T) -> Bool) -> T
            .add_constant("s0", "((T, T) -> Bool) -> T")
            // c1 is lt: T -> T -> Bool (after type application, it's (T, T) -> Bool)
            .add_constant("c1", "T -> T -> Bool");

        let mut clause_set = GeneralizationSet::new();

        // Pattern: not f(s0(f), s0(f)) or g1(Type)(f)
        // where f: (T, T) -> Bool (variable x0)
        // But we need the pattern to be g1(Type)(x0), not just g1(x0)
        // We'll need to construct this manually
        let type_atom = Atom::Symbol(Symbol::Type(GroundTypeId::new(0)));
        let type_term = Term::atom(type_atom);
        let g1_atom = Atom::Symbol(Symbol::GlobalConstant(1));
        let s0_atom = Atom::Symbol(Symbol::Synthetic(0));
        let x0_term = Term::new_variable(0);

        // First literal: not x0(s0(x0), s0(x0))
        let s0_x0 = Term::new(s0_atom, vec![x0_term.clone()]);
        let x0_s0_s0 = x0_term.apply(&[s0_x0.clone(), s0_x0.clone()]);
        let lit1_pattern = Literal {
            positive: false,
            left: x0_s0_s0,
            right: Term::new_true(),
        };

        // Second literal: g1(Type)(x0) = g1(Type, x0)
        let g1_type_x0 = Term::new(g1_atom, vec![type_term.clone(), x0_term.clone()]);
        let lit2_pattern = Literal {
            positive: true,
            left: g1_type_x0,
            right: Term::new_true(),
        };

        // The variable type for x0
        let var_type = kctx.parse_type("(T, T) -> Bool");
        let pattern_context = LocalContext::from_types(vec![var_type]);
        let pattern =
            Clause::from_literals_unnormalized(vec![lit1_pattern, lit2_pattern], &pattern_context);
        clause_set.insert(pattern.clone(), 99, &kctx);
        eprintln!("Inserted pattern: {:?}", pattern);

        // Build query: not g0(Type)(c1)(s0(...), s0(...)) or g1(Type)(g0(Type)(c1))
        let g0_atom = Atom::Symbol(Symbol::GlobalConstant(0));
        let c1_atom = Atom::Symbol(Symbol::ScopedConstant(1));
        let c1_term = Term::atom(c1_atom);

        // g0(Type)(c1) = g0(Type, c1)
        let g0_type_c1 = Term::new(g0_atom, vec![type_term.clone(), c1_term.clone()]);

        // s0(g0(Type)(c1))
        let s0_g0 = Term::new(s0_atom, vec![g0_type_c1.clone()]);

        // g0(Type, c1, s0(...), s0(...))
        let g0_type_c1_s0_s0 = Term::new(
            g0_atom,
            vec![
                type_term.clone(),
                c1_term.clone(),
                s0_g0.clone(),
                s0_g0.clone(),
            ],
        );

        // g1(Type, g0(Type, c1))
        let g1_type_g0 = Term::new(g1_atom, vec![type_term.clone(), g0_type_c1.clone()]);

        let lit1_query = Literal {
            positive: false,
            left: g0_type_c1_s0_s0,
            right: Term::new_true(),
        };

        let lit2_query = Literal {
            positive: true,
            left: g1_type_g0,
            right: Term::new_true(),
        };

        let query = Clause::from_literals_unnormalized(
            vec![lit1_query, lit2_query],
            &LocalContext::empty(),
        );
        eprintln!("Query: {:?}", query);

        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(
            found,
            Some(99),
            "Should match pattern with g1(Type)(f) against g1(Type)(g0(Type)(c1))"
        );
    }
}
