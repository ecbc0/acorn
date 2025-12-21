// The RewriteTree stores a set of potential rewrites.
// A given pattern can be rewritten to multiple different output terms.

use std::collections::HashMap;

use crate::kernel::atom::{Atom as KernelAtom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::pdt::{compute_unbound_var_remap, substitute_term, term_key_prefix, Pdt};
use crate::kernel::term::{Decomposition, Term, TermRef};

// Each term can correspond with multiple RewriteValues.
// This is the internal representation of the pattern, before it has been applied to a term.
#[derive(Clone)]
struct RewriteValue {
    // Which rule this rewrite is generated from
    pattern_id: usize,

    // For an s = t rule, "forwards" is rewriting s -> t, "backwards" is rewriting t -> s
    forwards: bool,

    // The pattern that we are rewriting into.
    // The pattern that we are rewriting *from* is kept in the key.
    output: Term,

    // Context for variables in the output term.
    output_context: LocalContext,
}

// The external representation of a rewrite, after it has been applied to a particular term.
#[derive(Clone)]
pub struct Rewrite {
    // Which rule this rewrite is generated from
    pub pattern_id: usize,

    // For an s = t rule, "forwards" is rewriting s -> t, "backwards" is rewriting t -> s
    pub forwards: bool,

    // The term that we are rewriting into.
    pub term: Term,

    // The context for variables in the rewritten term.
    // This is important for backwards rewrites where the context may differ from the original pattern.
    pub context: LocalContext,
}

/// Builds bindings from structural replacements, including inferred type variable bindings.
///
/// When a pattern variable's type is itself a type variable, and we've matched
/// the pattern variable to a concrete term, we can infer the type variable's
/// value from the matched term's type.
///
/// Example: Pattern variable x0 has type x1 where x1: Type.
/// If we match x0 → c1 where c1: T1, then x1 should be bound to T1.
///
/// Returns a HashMap mapping pattern variable IDs to their replacement terms.
fn build_bindings(
    structural_replacements: &[TermRef],
    pattern_context: &LocalContext,
    query_context: &LocalContext,
    kernel_context: &KernelContext,
) -> HashMap<AtomId, Term> {
    let mut bindings: HashMap<AtomId, Term> = HashMap::new();

    // Add structural replacements to bindings
    for (i, replacement) in structural_replacements.iter().enumerate() {
        bindings.insert(i as AtomId, replacement.to_owned());
    }

    // Infer type variable bindings from the types of matched terms
    for (i, replacement) in structural_replacements.iter().enumerate() {
        if let Some(var_type) = pattern_context.get_var_type(i) {
            // If the pattern variable's type is a FreeVariable (type variable)
            if let Decomposition::Atom(KernelAtom::FreeVariable(type_var_id)) =
                var_type.as_ref().decompose()
            {
                // Only infer if we haven't already bound this type variable
                if !bindings.contains_key(type_var_id) {
                    // Bind the type variable to the type of the matched term
                    let replacement_type =
                        replacement.get_type_with_context(query_context, kernel_context);
                    bindings.insert(*type_var_id, replacement_type);
                }
            }
        }
    }

    bindings
}

#[derive(Clone)]
pub struct RewriteTree {
    tree: Pdt<Vec<RewriteValue>>,
}

impl RewriteTree {
    pub fn new() -> RewriteTree {
        RewriteTree { tree: Pdt::new() }
    }

    // Inserts one direction.
    // NOTE: The input term's variable ids must be normalized.
    fn insert_terms(
        &mut self,
        pattern_id: usize,
        input_term: &Term,
        output_term: &Term,
        forwards: bool,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        if input_term.is_true() {
            panic!("cannot rewrite true to something else");
        }
        let value = RewriteValue {
            pattern_id,
            forwards,
            output: output_term.clone(),
            output_context: local_context.clone(),
        };
        Pdt::insert_or_append(
            &mut self.tree,
            input_term,
            value,
            local_context,
            kernel_context,
        );
    }

    // Inserts both directions.
    // NOTE: The input term's variable ids must be normalized.
    pub fn insert_literal(
        &mut self,
        pattern_id: usize,
        literal: &Literal,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        // Already normalized
        self.insert_terms(
            pattern_id,
            &literal.left,
            &literal.right,
            true,
            local_context,
            kernel_context,
        );

        if !literal.right.is_true() {
            let (mut right, mut left, reversed_context) =
                literal.normalized_reversed(local_context);

            // The PDT expects variables numbered by structural occurrence order (0, 1, 2, ...),
            // but normalized_reversed uses type-dependency ordering. We need to renumber
            // variables structurally for PDT matching to work correctly.
            let mut structural_var_ids: Vec<AtomId> = vec![];
            right.collect_structural_var_ids(&mut structural_var_ids);
            left.collect_structural_var_ids(&mut structural_var_ids);

            // Renumber variables in both terms
            right.apply_var_renumbering(&structural_var_ids, &[]);
            left.apply_var_renumbering(&structural_var_ids, &[]);

            // Remap the context to match the new variable ordering
            let structural_context = reversed_context.remap(&structural_var_ids);

            self.insert_terms(
                pattern_id,
                &right,
                &left,
                false,
                &structural_context,
                kernel_context,
            );
        }
    }

    // The callback is on (rule id, forwards, new term, new context).
    fn find_rewrites<F>(
        &self,
        input_term: TermRef,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
        next_var: AtomId,
        callback: &mut F,
    ) where
        F: FnMut(usize, bool, Term, LocalContext),
    {
        let mut key = term_key_prefix();
        let mut replacements: Vec<TermRef> = vec![];
        self.tree.find_term_matches_while(
            &mut key,
            &[input_term],
            local_context,
            kernel_context,
            &mut replacements,
            &mut |value_id, replacements| {
                for value in &self.tree.values[value_id] {
                    // Step 1: Build bindings from structural replacements + inferred type bindings
                    let bindings = build_bindings(
                        replacements,
                        &value.output_context,
                        local_context,
                        kernel_context,
                    );

                    // Step 2: Compute var_remap and output context for unbound variables
                    let (var_remap, new_context) = compute_unbound_var_remap(
                        &value.output,
                        &value.output_context,
                        &bindings,
                        next_var,
                    );

                    // Step 3: Substitute into output term
                    let new_term = substitute_term(&value.output, &bindings, &var_remap);

                    callback(value.pattern_id, value.forwards, new_term, new_context);
                }
                true
            },
        );
    }

    // Finds all the ways to rewrite the given term, at the root level.
    //
    // Sometimes rewrites have to create a new variable.
    // When we create new variables, we start numbering from next_var.
    //
    // Returns a list of (pattern_id, forwards, new_term) tuples.
    pub fn get_rewrites(
        &self,
        input_term: &Term,
        next_var: AtomId,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<Rewrite> {
        let mut answer = vec![];
        self.find_rewrites(
            input_term.as_ref(),
            local_context,
            kernel_context,
            next_var,
            &mut |pattern_id, forwards, term, context| {
                answer.push(Rewrite {
                    pattern_id,
                    forwards,
                    term,
                    context,
                });
            },
        );
        answer
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::atom::Atom;

    use super::*;

    #[test]
    fn test_rewrite_tree_atoms() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1"], "Bool");
        let lctx = kctx.parse_local(&[]);

        let mut tree = RewriteTree::new();
        tree.insert_terms(
            0,
            &Term::parse("c1"),
            &Term::parse("c0"),
            true,
            &lctx,
            &kctx,
        );
        let rewrites = tree.get_rewrites(&Term::parse("c1"), 0, &lctx, &kctx);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].term, Term::parse("c0"));
    }

    #[test]
    fn test_rewrite_tree_functions() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constants(&["c0", "c2"], "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree = RewriteTree::new();
        // Rewrite rule: g1(x0, c0) -> g0(x0, c0)
        tree.insert_terms(
            0,
            &Term::parse("g1(x0, c0)"),
            &Term::parse("g0(x0, c0)"),
            true,
            &lctx,
            &kctx,
        );

        // Query: g1(c2, c0) should rewrite to g0(c2, c0)
        let query_lctx = kctx.parse_local(&[]);
        let rewrites = tree.get_rewrites(&Term::parse("g1(c2, c0)"), 0, &query_lctx, &kctx);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].term, Term::parse("g0(c2, c0)"));
    }

    #[test]
    fn test_rewrite_tree_multiple_rewrites() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constant("g3", "(Bool, Bool) -> Bool")
            .parse_constant("g4", "(Bool, Bool) -> Bool")
            .parse_constants(&["c0", "c2"], "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree = RewriteTree::new();
        // Rule 1: g1(x0, c2) -> g3(x0, c0)
        tree.insert_terms(
            0,
            &Term::parse("g1(x0, c2)"),
            &Term::parse("g3(x0, c0)"),
            true,
            &lctx,
            &kctx,
        );
        // Rule 2: g1(c2, x0) -> g4(x0, c0)
        tree.insert_terms(
            1,
            &Term::parse("g1(c2, x0)"),
            &Term::parse("g4(x0, c0)"),
            true,
            &lctx,
            &kctx,
        );

        // Query: g1(c2, c2) should match both rules
        let query_lctx = kctx.parse_local(&[]);
        let rewrites = tree.get_rewrites(&Term::parse("g1(c2, c2)"), 0, &query_lctx, &kctx);
        assert_eq!(rewrites.len(), 2);
        assert_eq!(rewrites[0].term, Term::parse("g3(c2, c0)"));
        assert_eq!(rewrites[1].term, Term::parse("g4(c2, c0)"));
    }

    #[test]
    fn test_rewrite_tree_inserting_edge_literals() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool");

        let mut tree = RewriteTree::new();
        // x0 = c0 where both are Bool
        let clause1 = kctx.parse_clause("x0 = c0", &["Bool"]);
        tree.insert_literal(0, &clause1.literals[0], clause1.get_local_context(), &kctx);
        // c0 alone as literal (Bool = true)
        let clause2 = kctx.parse_clause("c0", &[]);
        tree.insert_literal(1, &clause2.literals[0], clause2.get_local_context(), &kctx);
    }

    #[test]
    fn test_new_variable_created_during_rewrite() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constants(&["c0", "c1"], "Bool");

        let mut tree = RewriteTree::new();
        // g1(x0, c1) = c0 means c0 rewrites to g1(x1, c1) with a new variable x1
        let clause = kctx.parse_clause("g1(x0, c1) = c0", &["Bool"]);
        tree.insert_literal(0, &clause.literals[0], clause.get_local_context(), &kctx);

        let query_lctx = kctx.parse_local(&[]);
        let rewrites = tree.get_rewrites(&Term::parse("c0"), 1, &query_lctx, &kctx);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].term, Term::parse("g1(x1, c1)"));
    }

    #[test]
    fn test_rewrite_tree_checks_type() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constant("c0", "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree = RewriteTree::new();
        // Make a rule for Bool-typed variables
        let var_bool = Term::atom(Atom::FreeVariable(0));
        tree.insert_terms(0, &var_bool, &var_bool, true, &lctx, &kctx);

        // A Bool constant should match it
        let query_lctx = kctx.parse_local(&[]);
        let const_bool = Term::parse("c0");
        let rewrites = tree.get_rewrites(&const_bool, 0, &query_lctx, &kctx);
        assert_eq!(rewrites.len(), 1);

        // A different type term should not match
        // g0 has type (Bool, Bool) -> Bool which is different from Bool
        let func_term = Term::parse("g0");
        let rewrites = tree.get_rewrites(&func_term, 0, &query_lctx, &kctx);
        assert_eq!(rewrites.len(), 0);
    }

    #[test]
    fn test_rewrite_tree_polymorphic_forward() {
        // Test forward rewriting with polymorphic types.
        // Pattern: g0(T, x) = x where T: Type, x: T
        // Query: g0(Foo, c1) should rewrite to c1

        let mut kctx = KernelContext::new();
        // Use "Foo" instead of "T1" to avoid conflict with type variable syntax (T0, T1, etc.)
        kctx.parse_datatype("Foo");
        kctx.parse_polymorphic_constant("g0", "T: Type", "T -> T");
        kctx.parse_constant("c1", "Foo");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("g0(x0, x1) = x1", &["Type", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
            &kctx,
        );

        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("g0(Foo, c1)");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // Filter for forward rewrites only (backwards rewrites also match but produce different results)
        let forward_rewrites: Vec<_> = rewrites.iter().filter(|r| r.forwards).collect();
        assert_eq!(forward_rewrites.len(), 1);
        assert_eq!(forward_rewrites[0].term, kctx.parse_term("c1"));
    }

    #[test]
    fn test_rewrite_tree_polymorphic_nested() {
        // Test forward rewriting with nested polymorphic functions.
        // Pattern: g1(T, g0(T, x)) = x
        // Query: g1(Foo, g0(Foo, c1)) should rewrite to c1

        let mut kctx = KernelContext::new();
        // Use "Foo" instead of "T1" to avoid conflict with type variable syntax (T0, T1, etc.)
        kctx.parse_datatype("Foo");
        kctx.parse_polymorphic_constant("g0", "T: Type", "T -> T");
        kctx.parse_polymorphic_constant("g1", "T: Type", "T -> T");
        kctx.parse_constant("c1", "Foo");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("g1(x0, g0(x0, x1)) = x1", &["Type", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
            &kctx,
        );

        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("g1(Foo, g0(Foo, c1))");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // Filter for forward rewrites only (backwards rewrites also match but produce different results)
        let forward_rewrites: Vec<_> = rewrites.iter().filter(|r| r.forwards).collect();
        assert_eq!(forward_rewrites.len(), 1);
        assert_eq!(forward_rewrites[0].term, kctx.parse_term("c1"));
    }

    #[test]
    fn test_rewrite_tree_polymorphic_backwards() {
        // Test backwards rewriting with polymorphic types.
        //
        // Pattern: g0(T, x) = x where T: Type, x: T
        // Backwards rewrite: x -> g0(T, x)
        //
        // When we rewrite c1 (type Foo) backwards, T should be inferred from
        // the type of the matched term. Result should be g0(Foo, c1).

        let mut kctx = KernelContext::new();
        // Use "Foo" instead of "T1" to avoid conflict with type variable syntax (T0, T1, etc.)
        kctx.parse_datatype("Foo");
        kctx.parse_polymorphic_constant("g0", "T: Type", "T -> T");
        kctx.parse_constant("c1", "Foo");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("g0(x0, x1) = x1", &["Type", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
            &kctx,
        );

        // Query: c1 (for backwards rewrite)
        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("c1");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // Should find a backwards rewrite
        assert_eq!(rewrites.len(), 1, "Should find one backwards rewrite");

        // The type variable T should be inferred from c1's type (Foo)
        let expected = kctx.parse_term("g0(Foo, c1)");
        assert_eq!(
            rewrites[0].term, expected,
            "Backwards rewrite should infer type variable from matched term's type"
        );
    }

    #[test]
    fn test_rewrite_tree_two_type_params_backwards() {
        // Test backwards rewriting with TWO type parameters (like Pair[T, U]).
        // This is more complex because we need to infer both T and U.
        //
        // Pattern: pair(T, U, x, y).first = x where T: Type, U: Type, x: T, y: U
        // Backwards rewrite: x -> pair(T, U, x, ???).first
        //
        // When we only have x, we can infer T from x's type, but we can't know
        // what U or y should be. They should remain as new variables.

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Foo");
        kctx.parse_datatype("Bar");
        kctx.parse_datatype("Result");
        // g0 = pair: (T: Type) -> (U: Type) -> T -> U -> Result
        kctx.parse_polymorphic_constant("g0", "T: Type, U: Type", "T -> U -> Result");
        // g1 = first: (T: Type) -> (U: Type) -> Result -> T
        kctx.parse_polymorphic_constant("g1", "T: Type, U: Type", "Result -> T");
        kctx.parse_constant("c1", "Foo");
        kctx.parse_constant("c2", "Bar");

        let mut tree = RewriteTree::new();

        // Pattern: g1(T, U, g0(T, U, x, y)) = x
        // In normalized form: g1(x0, x1, g0(x0, x1, x2, x3)) = x2
        // where x0: Type, x1: Type, x2: x0, x3: x1
        let pattern_clause =
            kctx.parse_clause("g1(x0, x1, g0(x0, x1, x2, x3)) = x2", &["Type", "Type", "x0", "x1"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
            &kctx,
        );

        // Query: c1 (for backwards rewrite)
        // We're trying to backwards-rewrite c1 to g1(..., g0(..., c1, ?))
        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("c1");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // Should find a backwards rewrite
        assert!(
            !rewrites.is_empty(),
            "Should find at least one backwards rewrite"
        );

        // Check the rewrite context is well-formed
        for rewrite in &rewrites {
            // The context should have proper types for all variables
            // In particular, if there are variables with type=FreeVariable(n),
            // then n should have type=Type
            for (i, var_type) in rewrite.context.get_var_types().iter().enumerate() {
                if let Decomposition::Atom(KernelAtom::FreeVariable(type_var_id)) =
                    var_type.as_ref().decompose()
                {
                    let type_var_idx = *type_var_id as usize;
                    let type_of_type_var = rewrite.context.get_var_type(type_var_idx);
                    assert!(
                        type_of_type_var.is_some(),
                        "Variable x{} has type x{}, but x{} has no type in context. Context: {:?}",
                        i,
                        type_var_id,
                        type_var_id,
                        rewrite.context.get_var_types()
                    );
                }
            }

            // Check that the term's type is well-formed with respect to its context
            let term_type = rewrite.term.get_type_with_context(&rewrite.context, &kctx);

            // Since we're rewriting c1 (type Foo), the output term should also have type Foo
            // The backwards rewrite produces g1(T, U, g0(T, U, c1, y)) where:
            // - T should be inferred as Foo (from c1's type)
            // - U is a new variable
            // - y is a new variable of type U
            //
            // The result type of g1(T, U, ...) should be T, which should be Foo.
            let expected_type = kctx.parse_type("Foo");
            assert_eq!(
                term_type, expected_type,
                "Rewritten term should have type Foo. Got: {:?}. Term: {}. Context: {:?}",
                term_type, rewrite.term, rewrite.context.get_var_types()
            );
        }
    }
}
