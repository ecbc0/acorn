//! Inference rules that work with both Fat and Thin clause representations.
//!
//! These functions implement the core inference rules used in theorem proving:
//! - Equality Resolution (ER)
//! - Equality Factoring (EF)
//!
//! They are generic over the clause representation through the type aliases.

use crate::kernel::aliases::{Clause, Literal};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::unifier::{Scope, Unifier};
use crate::proof_step::{EFLiteralTrace, EFTermTrace};

/// Finds all possible equality resolutions for a clause.
///
/// Equality resolution applies when a clause contains a negative literal `s != t`
/// where `s` and `t` can be unified. The literal is then removed from the clause.
///
/// Returns a vector of tuples containing:
/// - The index of the literal that was resolved
/// - The resulting literals after applying the unifier
/// - The flipped flags for each literal
/// - The output_context containing types of variables in the resulting literals
pub fn find_equality_resolutions(
    clause: &Clause,
    kernel_context: &KernelContext,
) -> Vec<(usize, Vec<Literal>, Vec<bool>, LocalContext)> {
    let mut results = vec![];

    for i in 0..clause.literals.len() {
        let literal = &clause.literals[i];
        if literal.positive {
            // Negative literals come before positive ones, so we're done
            break;
        }

        // The variables are in the same scope, which we will call "left".
        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, clause.get_local_context());
        if !unifier.unify(Scope::LEFT, &literal.left, Scope::LEFT, &literal.right) {
            continue;
        }

        // We can do equality resolution
        let mut new_literals = vec![];
        let mut flipped = vec![];
        for (j, lit) in clause.literals.iter().enumerate() {
            if j != i {
                let (new_lit, j_flipped) = unifier.apply_to_literal(Scope::LEFT, lit);
                new_literals.push(new_lit);
                flipped.push(j_flipped);
            }
        }

        // Get the output context from the unifier
        let output_context = unifier.take_output_context();

        // Return the raw literals without checking for tautology
        // The caller will handle that after normalization
        results.push((i, new_literals, flipped, output_context));
    }

    results
}

/// Generates all clauses that can be derived from a clause using equality resolution.
/// This is a convenience function that returns just the normalized clauses.
pub fn equality_resolutions(clause: &Clause, kernel_context: &KernelContext) -> Vec<Clause> {
    find_equality_resolutions(clause, kernel_context)
        .into_iter()
        .map(|(_, literals, _, context)| Clause::new(literals, &context))
        .filter(|c| !c.is_tautology())
        .collect()
}

/// Finds all possible equality factorings for a clause.
///
/// Equality factoring applies when a clause has two positive literals that can
/// be partially unified. It creates a new clause with an additional negative literal.
///
/// Returns a vector of (literals, ef_trace, output_context) tuples.
/// The literals are the result of factoring before normalization.
/// The ef_trace tracks how the literals were transformed.
/// The output_context contains types for variables in the resulting literals.
pub fn find_equality_factorings(
    clause: &Clause,
    kernel_context: &KernelContext,
) -> Vec<(Vec<Literal>, Vec<EFLiteralTrace>, LocalContext)> {
    let mut results = vec![];

    // The first literal must be positive for equality factoring
    if clause.literals.is_empty() || !clause.literals[0].positive {
        return results;
    }

    let st_literal = &clause.literals[0];

    for (st_forwards, s, t) in st_literal.both_term_pairs() {
        for i in 1..clause.literals.len() {
            let uv_literal = &clause.literals[i];
            if !uv_literal.positive {
                continue;
            }

            for (uv_forwards, u, v) in uv_literal.both_term_pairs() {
                let mut unifier = Unifier::new(3, kernel_context);
                unifier.set_input_context(Scope::LEFT, clause.get_local_context());
                if !unifier.unify(Scope::LEFT, s, Scope::LEFT, u) {
                    continue;
                }

                // Create the factored terms.
                let mut literals = vec![];
                let mut ef_trace = vec![];
                let (tv_lit, tv_flip) = Literal::new_with_flip(
                    false,
                    unifier.apply(Scope::LEFT, t),
                    unifier.apply(Scope::LEFT, v),
                );
                let (uv_out, uv_out_flip) = Literal::new_with_flip(
                    true,
                    unifier.apply(Scope::LEFT, u),
                    unifier.apply(Scope::LEFT, v),
                );

                literals.push(tv_lit);
                literals.push(uv_out);

                // Figure out where the factored terms went.
                // The output has two literals:
                // literals[0] = t != v (the new inequality)
                // literals[1] = u = v (the preserved equality, with s unified to u)

                // s and u both go to the left of u = v (they were unified)
                let s_out = EFTermTrace {
                    index: 1,
                    left: !uv_out_flip,
                };
                // t goes to the left of t != v
                let t_out = EFTermTrace {
                    index: 0,
                    left: !tv_flip,
                };
                // u goes to the same place as s
                let u_out = s_out;
                // v goes to the right of t != v
                let v_out = EFTermTrace {
                    index: 0,
                    left: tv_flip,
                };

                ef_trace.push(EFLiteralTrace::to_out(s_out, t_out, !st_forwards));

                for j in 1..clause.literals.len() {
                    if i == j {
                        ef_trace.push(EFLiteralTrace::to_out(u_out, v_out, !uv_forwards));
                    } else {
                        let (new_lit, j_flipped) =
                            unifier.apply_to_literal(Scope::LEFT, &clause.literals[j]);
                        let index = literals.len();
                        ef_trace.push(EFLiteralTrace::to_index(index, j_flipped));
                        literals.push(new_lit);
                    }
                }

                // Get the output context from the unifier
                let output_context = unifier.take_output_context();

                results.push((literals, ef_trace, output_context));
            }
        }
    }

    results
}

/// Generates all clauses that can be derived from a clause using equality factoring.
/// This is a convenience function that returns just the normalized clauses.
pub fn equality_factorings(
    clause: &Clause,
    _context: &LocalContext,
    kernel_context: &KernelContext,
) -> Vec<Clause> {
    find_equality_factorings(clause, kernel_context)
        .into_iter()
        .map(|(literals, _, output_context)| Clause::new(literals, &output_context))
        .filter(|c| !c.is_tautology())
        .collect()
}
