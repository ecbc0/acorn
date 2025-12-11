use std::cmp::Ordering;
use std::vec;

use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::pattern_tree::PatternTree;
use crate::kernel::term::TermRef;

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
        .get_closed_type_with_context(local_context, kernel_context)
        .cmp(&right.get_closed_type_with_context(local_context, kernel_context));
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
        .get_closed_type_with_context(local_context, kernel_context)
        .cmp(&right.get_closed_type_with_context(local_context, kernel_context));
    if type_cmp != Ordering::Equal {
        return Some(type_cmp);
    }

    // If heads are different atoms, we can compare them
    if left.get_head_atom() != right.get_head_atom() {
        return Some(left.get_head_atom().cmp(&right.get_head_atom()));
    }

    // Heads are the same, so recurse on arguments
    assert!(left.num_args() == right.num_args());
    for (l, r) in left.iter_args().zip(right.iter_args()) {
        match sub_invariant_term_cmp(l, false, r, false, local_context, kernel_context) {
            Some(Ordering::Equal) => continue,
            x => return x,
        };
    }

    Some(Ordering::Equal)
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
    use crate::kernel::closed_type::ClosedType;

    /// Creates a LocalContext with enough Bool-typed variables for tests.
    fn test_context() -> LocalContext {
        LocalContext::new_with_bools(10)
    }

    #[test]
    fn test_clause_set_basic_generalization() {
        // Using test_with_function_types():
        // - c0: (Bool, Bool) -> Bool
        // - c1: Bool -> Bool
        // - c5, c6, c7, c8, c9: Bool
        // - x0, x1, etc: Bool (from test_context)
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Insert a general clause with valid types:
        // c0(x0, c5) - c0 takes (Bool, Bool), x0:Bool, c5:Bool ✓
        // c1(x0) - c1 takes Bool, x0:Bool ✓
        let general_clause = Clause::parse("c0(x0, c5) or c1(x0)", &local);
        clause_set.insert(general_clause, 1, &ctx);

        // Test that a specialized version is recognized (x0 -> c6)
        let special_clause = Clause::parse("c1(c6) or c0(c6, c5)", &local);
        let result = clause_set.find_generalization(special_clause, &ctx);
        assert_eq!(result, Some(1), "Should find the generalization");
    }

    #[test]
    fn test_clause_set_reordered_literals() {
        // c0: (Bool, Bool) -> Bool, c1: Bool -> Bool, c5-c9: Bool
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Insert a clause with valid types:
        // c1(x0) - c1 takes Bool ✓
        // c0(x0, c5) - c0 takes (Bool, Bool) ✓
        let clause = Clause::parse("c1(x0) or c0(x0, c5)", &local);
        clause_set.insert(clause, 2, &ctx);

        // Test that reordered specializations are recognized (x0 -> c6)
        let special1 = Clause::parse("c0(c6, c5) or c1(c6)", &local);
        assert_eq!(clause_set.find_generalization(special1, &ctx), Some(2));

        // Another reordering (x0 -> c7)
        let special2 = Clause::parse("c1(c7) or c0(c7, c5)", &local);
        assert_eq!(clause_set.find_generalization(special2, &ctx), Some(2));
    }

    #[test]
    fn test_clause_set_flipped_equality() {
        // c0: (Bool, Bool) -> Bool, c1: Bool -> Bool, c5-c9: Bool
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Insert an equality clause with valid types:
        // x0 = c5 where both are Bool ✓
        // c1(x0) where c1 takes Bool ✓
        let clause = Clause::parse("x0 = c5 or c1(x0)", &local);
        clause_set.insert(clause, 3, &ctx);

        // Test that flipped equalities are recognized (x0 -> c6)
        let special = Clause::parse("c6 = c5 or c1(c6)", &local);
        assert_eq!(clause_set.find_generalization(special, &ctx), Some(3));

        // Also test with the equality already flipped (x0 -> c7)
        let special2 = Clause::parse("c5 = c7 or c1(c7)", &local);
        assert_eq!(clause_set.find_generalization(special2, &ctx), Some(3));
    }

    #[test]
    fn test_clause_set_no_generalization() {
        // c0: (Bool, Bool) -> Bool, c1: Bool -> Bool, c5-c9: Bool
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Insert a specific clause with valid types:
        // c0(c5, c6) - c0 takes (Bool, Bool) ✓
        // c1(c7) - c1 takes Bool ✓
        let clause = Clause::parse("c0(c5, c6) or c1(c7)", &local);
        clause_set.insert(clause, 4, &ctx);

        // Test clauses that should NOT have generalizations
        // Different second arg to c0
        let no_match1 = Clause::parse("c0(c5, c7) or c1(c7)", &local);
        assert_eq!(clause_set.find_generalization(no_match1, &ctx), None);

        // Swapped args to c0
        let no_match2 = Clause::parse("c0(c6, c5) or c1(c7)", &local);
        assert_eq!(clause_set.find_generalization(no_match2, &ctx), None);
    }

    #[test]
    fn test_clause_set_multiple_variables() {
        // c0: (Bool, Bool) -> Bool, c1: Bool -> Bool, c5-c9: Bool
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Insert a clause with multiple variables (valid types):
        // c0(x0, x1) - c0 takes (Bool, Bool), x0:Bool, x1:Bool ✓
        // c0(x1, x0) - same, just swapped ✓
        let clause = Clause::parse("c0(x0, x1) or c0(x1, x0)", &local);
        clause_set.insert(clause, 5, &ctx);

        // Test various specializations (x0 -> c5, x1 -> c6)
        let special1 = Clause::parse("c0(c5, c6) or c0(c6, c5)", &local);
        assert_eq!(clause_set.find_generalization(special1, &ctx), Some(5));

        // Reordered (x0 -> c7, x1 -> c8)
        let special2 = Clause::parse("c0(c8, c7) or c0(c7, c8)", &local);
        assert_eq!(clause_set.find_generalization(special2, &ctx), Some(5));

        // This should NOT match because the variable pattern is different
        // (different constants in each literal, doesn't match x0/x1 pattern)
        let no_match = Clause::parse("c0(c5, c6) or c0(c7, c8)", &local);
        assert_eq!(clause_set.find_generalization(no_match, &ctx), None);
    }

    #[test]
    fn test_clause_set_single_literal() {
        // Using test_with_function_types():
        // - c0: (Bool, Bool) -> Bool
        // - c5, c6, c7, c8, c9: Bool
        // - x0, x1, etc: Bool (from test_context)
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Insert single literal clauses with valid types
        // c0(x0, c5) where x0:Bool, c5:Bool, result:Bool
        let clause1 = Clause::parse("c0(x0, c5)", &local);
        clause_set.insert(clause1, 6, &ctx);

        // x0 = c5 where both are Bool
        let clause2 = Clause::parse("x0 = c5", &local);
        clause_set.insert(clause2, 7, &ctx);

        // Test specializations
        // c0(c6, c5) should match c0(x0, c5) with x0 -> c6
        assert_eq!(
            clause_set.find_generalization(Clause::parse("c0(c6, c5)", &local), &ctx),
            Some(6)
        );
        // c6 = c5 should match x0 = c5 with x0 -> c6
        assert_eq!(
            clause_set.find_generalization(Clause::parse("c6 = c5", &local), &ctx),
            Some(7)
        );
        // c5 = c6 should also match x0 = c5 (equality is symmetric)
        assert_eq!(
            clause_set.find_generalization(Clause::parse("c5 = c6", &local), &ctx),
            Some(7)
        );
    }

    #[test]
    fn test_clause_set_negated_literals() {
        // c5-c9: Bool, x0-x9: Bool
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Insert a clause with negated literals (all Bool types)
        let clause = Clause::parse("c5 = x0 or x1 != c6", &local);
        clause_set.insert(clause, 1, &ctx);

        // Test that it matches correct specializations (x0 -> c7, x1 -> c8)
        let special1 = Clause::parse("c5 = c7 or c8 != c6", &local);
        assert_eq!(clause_set.find_generalization(special1, &ctx), Some(1));

        // Test with reordered literals (x0 -> c7, x1 -> c7)
        let special2 = Clause::parse("c7 != c6 or c5 = c7", &local);
        assert_eq!(clause_set.find_generalization(special2, &ctx), Some(1));

        // Test with flipped inequality (x0 -> c8, x1 -> c8)
        let special3 = Clause::parse("c5 = c8 or c6 != c8", &local);
        assert_eq!(clause_set.find_generalization(special3, &ctx), Some(1));
    }

    #[test]
    fn test_clause_set_no_positive_negative_confusion() {
        // c5-c9: Bool, x0-x9: Bool
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Insert a clause with a positive literal (all Bool types)
        let positive_clause = Clause::parse("x0 = c5", &local);
        clause_set.insert(positive_clause, 1, &ctx);

        // Insert a clause with a negative literal
        let negative_clause = Clause::parse("x0 != c6", &local);
        clause_set.insert(negative_clause, 2, &ctx);

        // Test that positive matches positive (x0 -> c7)
        assert_eq!(
            clause_set.find_generalization(Clause::parse("c7 = c5", &local), &ctx),
            Some(1)
        );

        // Test that negative matches negative (x0 -> c8)
        assert_eq!(
            clause_set.find_generalization(Clause::parse("c8 != c6", &local), &ctx),
            Some(2)
        );

        // Test that positive does NOT match negative
        assert_eq!(
            clause_set.find_generalization(Clause::parse("c7 != c5", &local), &ctx),
            None
        );

        // Test that negative does NOT match positive
        assert_eq!(
            clause_set.find_generalization(Clause::parse("c8 = c6", &local), &ctx),
            None
        );
    }

    #[test]
    fn test_clause_set_mixed_positive_negative() {
        // c0: (Bool, Bool) -> Bool, c1: Bool -> Bool, c5-c9: Bool
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Insert a clause with both positive and negative literals (valid types):
        // not c1(x0) - c1 takes Bool, negated ✓
        // c0(x0, x1) - c0 takes (Bool, Bool) ✓
        // x1 != c5 - Bool != Bool ✓
        let clause = Clause::parse("not c1(x0) or c0(x0, x1) or x1 != c5", &local);
        clause_set.insert(clause, 1, &ctx);

        // Test various specializations (x0 -> c6, x1 -> c7)
        let special1 = Clause::parse("not c1(c6) or c0(c6, c7) or c7 != c5", &local);
        assert_eq!(clause_set.find_generalization(special1, &ctx), Some(1));

        // Test with reordering (x0 -> c8, x1 -> c9)
        let special2 = Clause::parse("c0(c8, c9) or c9 != c5 or not c1(c8)", &local);
        assert_eq!(clause_set.find_generalization(special2, &ctx), Some(1));

        // Test that wrong signs don't match
        let wrong1 = Clause::parse("c1(c6) or c0(c6, c7) or c7 != c5", &local); // First literal should be negative
        assert_eq!(clause_set.find_generalization(wrong1, &ctx), None);

        let wrong2 = Clause::parse("not c1(c6) or not c0(c6, c7) or c7 != c5", &local); // Second literal should be positive
        assert_eq!(clause_set.find_generalization(wrong2, &ctx), None);
    }

    #[test]
    fn test_clause_set_all_negative() {
        // c5-c9: Bool, x0-x9: Bool
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Insert a clause with only inequality literals (all Bool types)
        let clause = Clause::parse("x0 != c5 or x1 != c6 or x0 != x1", &local);
        clause_set.insert(clause, 1, &ctx);

        // Test that it matches (x0 -> c7, x1 -> c8)
        let special = Clause::parse("c7 != c5 or c8 != c6 or c7 != c8", &local);
        assert_eq!(clause_set.find_generalization(special, &ctx), Some(1));

        // Test with reordering (x0 -> c7, x1 -> c8)
        let special2 = Clause::parse("c7 != c8 or c7 != c5 or c8 != c6", &local);
        assert_eq!(clause_set.find_generalization(special2, &ctx), Some(1));
    }

    #[test]
    fn test_clause_set_boolean_negation() {
        // c0: (Bool, Bool) -> Bool, c1: Bool -> Bool, c5-c9: Bool
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();

        // Test with boolean negation (not) - valid types:
        // not c0(x0, c5) - c0 takes (Bool, Bool), negated ✓
        // c1(x0) - c1 takes Bool ✓
        let clause = Clause::parse("not c0(x0, c5) or c1(x0)", &local);
        clause_set.insert(clause, 1, &ctx);

        // Test that it matches (x0 -> c6)
        let special = Clause::parse("not c0(c6, c5) or c1(c6)", &local);
        assert_eq!(clause_set.find_generalization(special, &ctx), Some(1));

        // Test reordering (x0 -> c7)
        let special2 = Clause::parse("c1(c7) or not c0(c7, c5)", &local);
        assert_eq!(clause_set.find_generalization(special2, &ctx), Some(1));

        // Test that signs matter
        let wrong = Clause::parse("c0(c6, c5) or c1(c6)", &local); // Missing "not"
        assert_eq!(clause_set.find_generalization(wrong, &ctx), None);
    }

    #[test]
    fn test_clause_set_compound_generalization() {
        // g0: (Bool, Bool) -> Bool, g1: Bool -> Bool, c5-c9: Bool
        let ctx = KernelContext::test_with_function_types();
        let local = test_context();
        let mut clause_set = GeneralizationSet::new();
        // g0(c5, x0) = x0 where g0 takes (Bool, Bool), x0:Bool ✓
        let general = Clause::parse("g0(c5, x0) = x0", &local);
        clause_set.insert(general, 1, &ctx);
        // Specialization: g0(c5, g0(c6, c7)) = g0(c6, c7)
        let special = Clause::parse("g0(c5, g0(c6, c7)) = g0(c6, c7)", &local);
        assert_eq!(clause_set.find_generalization(special, &ctx), Some(1));
    }

    #[test]
    fn test_clause_set_with_applied_variable() {
        // Test GeneralizationSet with applied variables (variables in function position).
        // This exercises the PatternTree's ability to handle applied variables.
        //
        // Pattern: not x0(c5) or x0(x1)
        //   where x0: Bool -> Bool, x1: Bool
        //
        // Query: not c1(c5) or c1(c6)
        //   where c1: Bool -> Bool, c5, c6: Bool
        //
        // This should match with x0 -> c1, x1 -> c6
        use crate::kernel::symbol::Symbol;

        let kernel_context = KernelContext::test_with_function_types();

        // Create local context where x0 has type Bool -> Bool and x1 has type Bool
        let type_bool_to_bool = kernel_context
            .symbol_table
            .get_closed_type(Symbol::ScopedConstant(1)) // c1 has type Bool -> Bool
            .clone();
        let local_context =
            LocalContext::from_closed_types(vec![type_bool_to_bool, ClosedType::bool()]);

        let mut clause_set = GeneralizationSet::new();

        // Insert pattern: not x0(c5) or x0(x1)
        let pattern = Clause::parse("not x0(c5) or x0(x1)", &local_context);
        clause_set.insert(pattern, 42, &kernel_context);

        // Query: not c1(c5) or c1(c6)
        let query_local = LocalContext::empty();
        let query = Clause::parse("not c1(c5) or c1(c6)", &query_local);

        // This should find the pattern with x0 -> c1, x1 -> c6
        let found = clause_set.find_generalization(query, &kernel_context);
        assert_eq!(found, Some(42), "Should match clause with applied variable");
    }

    #[test]
    fn test_clause_set_with_applied_variable_nested_arg() {
        // Test case mirroring strong_induction usage:
        // Pattern: not g0(x0, x1) or x0(x1)
        //   where g0: (Bool -> Bool, Bool) -> Bool (like true_below)
        //         x0: Bool -> Bool
        //         x1: Bool
        //
        // Query: not g0(c1, c1(c5)) or c1(c1(c5))
        //   where c1: Bool -> Bool, c5: Bool
        //
        // This should match with x0 -> c1, x1 -> c1(c5)
        // This is the pattern from strong_induction: true_below(f, k) implies f(k)
        use crate::kernel::symbol::Symbol;

        let kernel_context = KernelContext::test_with_function_types();

        // Create local context where x0 has type Bool -> Bool and x1 has type Bool
        let type_bool_to_bool = kernel_context
            .symbol_table
            .get_closed_type(Symbol::ScopedConstant(1)) // c1 has type Bool -> Bool
            .clone();
        let local_context =
            LocalContext::from_closed_types(vec![type_bool_to_bool, ClosedType::bool()]);

        let mut clause_set = GeneralizationSet::new();

        // Insert pattern: not g0(x0, x1) or x0(x1)
        // g0: (Bool -> Bool, Bool) -> Bool takes two args
        // x0: Bool -> Bool (function variable)
        // x1: Bool (value variable)
        let pattern = Clause::parse("not g0(x0, x1) or x0(x1)", &local_context);
        clause_set.insert(pattern, 42, &kernel_context);

        // Query: not g0(c1, c1(c5)) or c1(c1(c5))
        // Here x0 -> c1, x1 -> c1(c5)
        let query_local = LocalContext::empty();
        let query = Clause::parse("not g0(c1, c1(c5)) or c1(c1(c5))", &query_local);

        // This should match with x0 -> c1, x1 -> c1(c5)
        let found = clause_set.find_generalization(query, &kernel_context);
        assert_eq!(
            found,
            Some(42),
            "Should match clause with applied variable and nested arg"
        );
    }

    #[test]
    fn test_clause_set_strong_induction_pattern() {
        // Exact pattern from strong_induction that's failing:
        // Pattern: not g10(x0, x1) or x0(x1)
        //   where g10: (Bool -> Bool, Bool) -> Bool (like true_below)
        //         x0: Bool -> Bool (function variable appearing as arg in first lit, func in second)
        //         x1: Bool
        //
        // Query: not g10(c1, c5) or c1(c5)
        //   where c1: Bool -> Bool, c5: Bool
        //
        // This should match with x0 -> c1, x1 -> c5
        use crate::kernel::symbol::Symbol;

        let kernel_context = KernelContext::test_with_function_types();

        // Create local context where x0 has type Bool -> Bool and x1 has type Bool
        let type_bool_to_bool = kernel_context
            .symbol_table
            .get_closed_type(Symbol::ScopedConstant(1)) // c1 has type Bool -> Bool
            .clone();
        let local_context =
            LocalContext::from_closed_types(vec![type_bool_to_bool, ClosedType::bool()]);

        let mut clause_set = GeneralizationSet::new();

        // Insert pattern: not g10(x0, x1) or x0(x1)
        // g10 has type (Bool -> Bool, Bool) -> Bool
        let pattern = Clause::parse("not g10(x0, x1) or x0(x1)", &local_context);
        clause_set.insert(pattern, 42, &kernel_context);

        // Query: not g10(c1, c5) or c1(c5) - simpler case first
        let query_local = LocalContext::empty();
        let query = Clause::parse("not g10(c1, c5) or c1(c5)", &query_local);

        let found = clause_set.find_generalization(query, &kernel_context);
        assert_eq!(
            found,
            Some(42),
            "Should match strong_induction pattern with x0 -> c1, x1 -> c5"
        );
    }

    #[test]
    fn test_pattern_tree_with_higher_order_types() {
        // Test PatternTree with higher-order function types.
        //
        // Pattern: not g10(x0, x1) or x0(x1)
        //   where g10: (Bool -> Bool, Bool) -> Bool (like true_below)
        //         x0: Bool -> Bool
        //         x1: Bool
        //
        // Query: not g10(c1, c5) or c1(c5)
        //
        // Tests that PatternTree correctly matches when x0 appears
        // both as an argument (to g10) and as a function (in x0(x1)).
        use crate::kernel::symbol::Symbol;

        let kernel_context = KernelContext::test_with_function_types();

        // Create local context where x0 has type Bool -> Bool and x1 has type Bool
        let type_bool_to_bool = kernel_context
            .symbol_table
            .get_closed_type(Symbol::ScopedConstant(1)) // c1 has type Bool -> Bool
            .clone();
        let local_context =
            LocalContext::from_closed_types(vec![type_bool_to_bool, ClosedType::bool()]);

        let mut clause_set = GeneralizationSet::new();

        // Insert pattern: not g10(x0, x1) or x0(x1)
        // g10 has type (Bool -> Bool, Bool) -> Bool
        let pattern = Clause::parse("not g10(x0, x1) or x0(x1)", &local_context);
        clause_set.insert(pattern, 42, &kernel_context);

        // Query: not g10(c1, c5) or c1(c5)
        let query_local = LocalContext::empty();
        let query = Clause::parse("not g10(c1, c5) or c1(c5)", &query_local);

        let found = clause_set.find_generalization(query, &kernel_context);
        assert_eq!(
            found,
            Some(42),
            "PatternTree should match strong_induction pattern"
        );
    }

    #[test]
    fn test_pattern_tree_with_nested_arg() {
        // Test with nested argument structure (like strong_induction with skolem).
        //
        // Pattern: not g10(x0, x1) or x0(x1)
        //   where g10: (Bool -> Bool, Bool) -> Bool (like true_below)
        //         x0: Bool -> Bool
        //         x1: Bool
        //
        // Query: not g10(c1, g11(c1)) or c1(g11(c1))
        //   where g11: (Bool -> Bool) -> Bool (like a skolem s0)
        //
        // The match should be: x0 -> c1, x1 -> g11(c1)
        use crate::kernel::symbol::Symbol;

        let kernel_context = KernelContext::test_with_function_types();

        // Create local context where x0 has type Bool -> Bool and x1 has type Bool
        let type_bool_to_bool = kernel_context
            .symbol_table
            .get_closed_type(Symbol::ScopedConstant(1)) // c1 has type Bool -> Bool
            .clone();
        let local_context =
            LocalContext::from_closed_types(vec![type_bool_to_bool, ClosedType::bool()]);

        let mut clause_set = GeneralizationSet::new();

        // Insert pattern: not g10(x0, x1) or x0(x1)
        // g10 has type (Bool -> Bool, Bool) -> Bool
        let pattern = Clause::parse("not g10(x0, x1) or x0(x1)", &local_context);
        clause_set.insert(pattern, 42, &kernel_context);

        // Query: not g10(c1, g11(c1)) or c1(g11(c1))
        // g11 has type (Bool -> Bool) -> Bool
        let query_local = LocalContext::empty();
        let query = Clause::parse("not g10(c1, g11(c1)) or c1(g11(c1))", &query_local);

        let found = clause_set.find_generalization(query, &kernel_context);
        assert_eq!(
            found,
            Some(42),
            "PatternTree should match pattern with nested arg"
        );
    }

    #[test]
    fn test_pattern_tree_rejects_sign_mismatch() {
        // Test that PatternTree correctly rejects clauses with mismatched literal signs.
        //
        // Pattern: g10(x0, x1) or x0(x1)  -- signs [true, true] (both positive)
        // Query: not g10(c1, c5) or c1(c5)  -- signs [false, true] (first negative)
        //
        // These should NOT match because the first literal has opposite signs.
        use crate::kernel::symbol::Symbol;

        let kernel_context = KernelContext::test_with_function_types();

        // Create local context where x0 has type Bool -> Bool and x1 has type Bool
        let type_bool_to_bool = kernel_context
            .symbol_table
            .get_closed_type(Symbol::ScopedConstant(1)) // c1 has type Bool -> Bool
            .clone();
        let local_context =
            LocalContext::from_closed_types(vec![type_bool_to_bool, ClosedType::bool()]);

        let mut clause_set = GeneralizationSet::new();

        // Insert pattern with POSITIVE first literal: g10(x0, x1) or x0(x1)
        // Note: no "not" on the first literal
        let pattern = Clause::parse("g10(x0, x1) or x0(x1)", &local_context);
        clause_set.insert(pattern, 42, &kernel_context);

        // Query with NEGATIVE first literal: not g10(c1, c5) or c1(c5)
        let query_local = LocalContext::empty();
        let query = Clause::parse("not g10(c1, c5) or c1(c5)", &query_local);

        // This should NOT match because the signs are different
        let found = clause_set.find_generalization(query, &kernel_context);
        assert_eq!(
            found, None,
            "Should NOT match when signs are different (first literal positive vs negative)"
        );
    }
}
