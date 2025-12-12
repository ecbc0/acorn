use std::cmp::Ordering;
use std::vec;

use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::pattern_tree::PatternTree;
#[cfg(test)]
use crate::kernel::term::Term;
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
        use crate::kernel::symbol::Symbol;

        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "Bool") // placeholder
            .add_constant("c1", "Bool -> Bool")
            .add_constants(&["c2", "c3", "c4", "c5", "c6"], "Bool");

        // Create local context where x0 has type Bool -> Bool and x1 has type Bool
        let type_bool_to_bool = kctx
            .symbol_table
            .get_type(Symbol::ScopedConstant(1))
            .clone();
        let lctx = LocalContext::from_types(vec![type_bool_to_bool, Term::type_bool()]);

        let mut clause_set = GeneralizationSet::new();

        let pattern = Clause::old_parse("not x0(c5) or x0(x1)", lctx.clone(), &kctx);
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
        use crate::kernel::symbol::Symbol;

        let mut kctx = KernelContext::new();
        // c0: (Bool -> Bool, Bool) -> Bool (higher order function)
        kctx.add_constant("c0", "(Bool -> Bool, Bool) -> Bool")
            .add_constant("c1", "Bool -> Bool")
            .add_constants(&["c2", "c3", "c4", "c5", "c6"], "Bool");

        // Create local context where x0 has type Bool -> Bool and x1 has type Bool
        let type_bool_to_bool = kctx
            .symbol_table
            .get_type(Symbol::ScopedConstant(1))
            .clone();
        let lctx = LocalContext::from_types(vec![type_bool_to_bool, Term::type_bool()]);

        let mut clause_set = GeneralizationSet::new();

        let pattern = Clause::old_parse("not c0(x0, x1) or x0(x1)", lctx.clone(), &kctx);
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
        use crate::kernel::symbol::Symbol;

        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "(Bool -> Bool, Bool) -> Bool")
            .add_constant("c1", "Bool -> Bool")
            .add_constant("c5", "Bool");

        let type_bool_to_bool = kctx
            .symbol_table
            .get_type(Symbol::ScopedConstant(1))
            .clone();
        let lctx = LocalContext::from_types(vec![type_bool_to_bool, Term::type_bool()]);

        let mut clause_set = GeneralizationSet::new();

        // Insert pattern with POSITIVE first literal
        let pattern = Clause::old_parse("c0(x0, x1) or x0(x1)", lctx.clone(), &kctx);
        clause_set.insert(pattern, 42, &kctx);

        // Query with NEGATIVE first literal
        let query = kctx.make_clause("not c0(c1, c5) or c1(c5)", &[]);
        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(found, None, "Should NOT match when signs are different");
    }
}
