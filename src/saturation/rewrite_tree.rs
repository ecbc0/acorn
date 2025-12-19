// The RewriteTree stores a set of potential rewrites.
// A given pattern can be rewritten to multiple different output terms.

use crate::kernel::atom::AtomId;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
#[cfg(not(feature = "pdt"))]
use crate::kernel::pattern_tree::{replace_term_variables, term_key_prefix, PatternTree};
#[cfg(feature = "pdt")]
use crate::kernel::pdt::{replace_term_variables, term_key_prefix, PatternTree};
use crate::kernel::term::Term;
use crate::kernel::term::TermRef;

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

#[derive(Clone)]
pub struct RewriteTree {
    tree: PatternTree<Vec<RewriteValue>>,
}

impl RewriteTree {
    pub fn new() -> RewriteTree {
        RewriteTree {
            tree: PatternTree::new(),
        }
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
        PatternTree::insert_or_append(
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
            let (right, left, reversed_context) = literal.normalized_reversed(local_context);
            self.insert_terms(
                pattern_id,
                &right,
                &left,
                false,
                &reversed_context,
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
                    let (new_term, new_context) = replace_term_variables(
                        &value.output,
                        &value.output_context,
                        replacements,
                        local_context,
                        Some(next_var),
                    );
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
}
