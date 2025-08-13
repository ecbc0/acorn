use std::fmt;

use crate::atom::{Atom, AtomId};
use crate::literal::Literal;
use crate::proof_step::{EFLiteralTrace, EFTermTrace};
use crate::unifier::{Scope, Unifier};

// A record of what happened to a single literal during a single proof step.
// This includes simplification and resolution, but not every sort of deduction.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum LiteralTrace {
    // This literal is in the output clause.
    Output { index: usize, flipped: bool },

    // This literal was eliminated by combining with the given step.
    // Step must be a single literal.
    Eliminated { step: usize, flipped: bool },

    // This literal was self-contradictory, of the form x != x.
    Impossible,
}

impl LiteralTrace {
    fn flip(&mut self) {
        match self {
            LiteralTrace::Output { flipped, .. } => *flipped = !*flipped,
            LiteralTrace::Eliminated { flipped, .. } => *flipped = !*flipped,
            LiteralTrace::Impossible => {}
        }
    }

    pub fn step_id(&self) -> Option<usize> {
        match self {
            LiteralTrace::Eliminated { step, .. } => Some(*step),
            _ => None,
        }
    }
}

// Modifies the first trace in place.
fn compose_traces(first: &mut Vec<LiteralTrace>, second: &Vec<LiteralTrace>) {
    for i in 0..first.len() {
        let LiteralTrace::Output { index, flipped } = first[i] else {
            continue;
        };
        first[i] = second[index].clone();
        if flipped {
            first[i].flip();
        }
    }
}

/// A clause is a disjunction (an "or") of literals, universally quantified over some variables.
/// We include the types of the universal variables it is quantified over.
/// It cannot contain existential quantifiers.
#[derive(Debug, Eq, PartialEq, Hash, Clone, Ord, PartialOrd)]
pub struct Clause {
    pub literals: Vec<Literal>,
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.literals.is_empty() {
            return write!(f, "<empty>");
        }
        for (i, literal) in self.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " or ")?;
            }
            write!(f, "{}", literal)?;
        }
        Ok(())
    }
}

impl Clause {
    /// Sorts literals.
    /// Removes any duplicate or impossible literals.
    /// An empty clause indicates an impossible clause.
    pub fn new(literals: Vec<Literal>) -> Clause {
        let mut c = Clause::new_without_normalizing_ids(literals);
        c.normalize_var_ids();
        c
    }

    pub fn new_without_normalizing_ids(literals: Vec<Literal>) -> Clause {
        let mut literals = literals
            .into_iter()
            .filter(|x| !x.is_impossible())
            .collect::<Vec<_>>();
        literals.sort();
        literals.dedup();
        Clause { literals }
    }

    /// Normalizes literals into a clause, creating a trace of where each one is sent.
    /// Note that this doesn't flip any literals. It only creates the "Output" and "Impossible"
    /// type traces.
    pub fn normalize_with_trace(literals: Vec<Literal>) -> (Clause, Vec<LiteralTrace>) {
        let mut trace = vec![LiteralTrace::Impossible; literals.len()];

        // Pair each literal with its initial index.
        let mut indexed_literals: Vec<(Literal, usize)> = literals
            .into_iter()
            .enumerate()
            .filter_map(|(i, lit)| {
                if lit.is_impossible() {
                    None
                } else {
                    Some((lit, i))
                }
            })
            .collect();
        indexed_literals.sort();

        let mut output_literals = vec![];
        for (literal, input_index) in indexed_literals {
            if !output_literals.is_empty() {
                let last_index = output_literals.len() - 1;
                if literal == output_literals[last_index] {
                    // This literal is a duplicate, but it is in the output.
                    trace[input_index] = LiteralTrace::Output {
                        index: last_index,
                        flipped: false,
                    };
                    continue;
                }
            }
            let output_index = output_literals.len();
            output_literals.push(literal);
            trace[input_index] = LiteralTrace::Output {
                index: output_index,
                flipped: false,
            };
        }
        let mut c = Clause {
            literals: output_literals,
        };
        c.normalize_var_ids();
        (c, trace)
    }

    /// Creates a new clause and a new trace, given a list of literals and a
    /// trace of how they were created.
    pub fn new_with_trace(
        literals: Vec<Literal>,
        mut traces: Vec<LiteralTrace>,
    ) -> (Clause, Vec<LiteralTrace>) {
        let (c, incremental_trace) = Clause::normalize_with_trace(literals);
        compose_traces(&mut traces, &incremental_trace);
        (c, traces)
    }

    /// Creates a new clause. If a trace is provided, we compose the traces.
    /// The base_trace should be applicable to the provided literals.
    pub fn new_composing_traces(
        literals: Vec<Literal>,
        base_traces: Option<Vec<LiteralTrace>>,
        incremental_trace: &Vec<LiteralTrace>,
    ) -> (Clause, Option<Vec<LiteralTrace>>) {
        let Some(mut base_traces) = base_traces else {
            return (Clause::new(literals), None);
        };
        compose_traces(&mut base_traces, incremental_trace);
        let (c, traces) = Clause::new_with_trace(literals, base_traces);
        (c, Some(traces))
    }

    pub fn from_literal(literal: Literal, flipped: bool) -> (Clause, Vec<LiteralTrace>) {
        Clause::new_with_trace(
            vec![literal],
            vec![LiteralTrace::Output { index: 0, flipped }],
        )
    }

    /// Normalizes the variable IDs in the literals.
    /// If you reorder or modify the literals, you should call this.
    pub fn normalize_var_ids(&mut self) {
        let mut var_ids = vec![];
        for literal in &mut self.literals {
            literal.left.normalize_var_ids(&mut var_ids);
            literal.right.normalize_var_ids(&mut var_ids);
        }
    }

    /// An unsatisfiable clause. Like a lone "false".
    pub fn impossible() -> Clause {
        Clause::new(vec![])
    }

    pub fn parse(s: &str) -> Clause {
        Clause::new(
            s.split(" or ")
                .map(|x| Literal::parse(x))
                .collect::<Vec<_>>(),
        )
    }

    pub fn is_tautology(&self) -> bool {
        // Find the index of the first positive literal
        if let Some(first_pos) = self.literals.iter().position(|x| x.positive) {
            // Check for (!p, p) pairs which cause a tautology
            for neg_literal in &self.literals[0..first_pos] {
                for pos_literal in &self.literals[first_pos..] {
                    if neg_literal.left == pos_literal.left
                        && neg_literal.right == pos_literal.right
                    {
                        return true;
                    }
                }
            }
        }

        self.literals.iter().any(|x| x.is_tautology())
    }

    pub fn is_impossible(&self) -> bool {
        self.literals.is_empty()
    }

    pub fn atom_count(&self) -> u32 {
        self.literals.iter().map(|x| x.atom_count()).sum()
    }

    pub fn len(&self) -> usize {
        self.literals.len()
    }

    pub fn has_any_variable(&self) -> bool {
        self.literals.iter().any(|x| x.has_any_variable())
    }

    pub fn has_skolem(&self) -> bool {
        self.literals.iter().any(|x| x.has_skolem())
    }

    pub fn has_local_constant(&self) -> bool {
        self.literals.iter().any(|x| x.has_local_constant())
    }

    pub fn num_positive_literals(&self) -> usize {
        self.literals.iter().filter(|x| x.positive).count()
    }

    pub fn least_unused_variable(&self) -> AtomId {
        self.literals
            .iter()
            .map(|x| x.least_unused_variable())
            .max()
            .unwrap_or(0)
    }

    /// Whether every literal in this clause is exactly contained by the other clause.
    pub fn contains(&self, other: &Clause) -> bool {
        for literal in &other.literals {
            if !self.literals.iter().any(|x| x == literal) {
                return false;
            }
        }
        true
    }

    /// Whether any top level term has the given atom as its head.
    pub fn has_head(&self, atom: &Atom) -> bool {
        self.literals.iter().any(|x| x.has_head(atom))
    }

    /// Whether we are willing to turn this clause into a line of code in a proof.
    pub fn is_printable(&self) -> bool {
        if self.len() > 1 {
            return false;
        }
        if self.has_skolem() {
            return false;
        }
        true
    }

    /// Converts atoms from the given list to variables, and shifts existing variables to make room.
    pub fn convert_to_variable(&self, from: &[Atom]) -> Clause {
        let new_literals = self
            .literals
            .iter()
            .map(|lit| lit.convert_to_variable(from))
            .collect();
        Clause {
            literals: new_literals,
        }
    }

    /// Finds all possible equality resolutions for this clause.
    /// Returns a vector of tuples containing:
    /// - The index of the literal that was resolved
    /// - The resulting literals after applying the unifier
    /// - The flipped flags for each literal
    pub fn find_equality_resolutions(&self) -> Vec<(usize, Vec<Literal>, Vec<bool>)> {
        let mut results = vec![];

        for i in 0..self.literals.len() {
            let literal = &self.literals[i];
            if literal.positive {
                // Negative literals come before positive ones, so we're done
                break;
            }

            // The variables are in the same scope, which we will call "left".
            let mut unifier = Unifier::new(3);
            if !unifier.unify(Scope::LEFT, &literal.left, Scope::LEFT, &literal.right) {
                continue;
            }

            // We can do equality resolution
            let mut new_literals = vec![];
            let mut flipped = vec![];
            for (j, lit) in self.literals.iter().enumerate() {
                if j != i {
                    let (new_lit, j_flipped) = unifier.apply_to_literal(Scope::LEFT, lit);
                    new_literals.push(new_lit);
                    flipped.push(j_flipped);
                }
            }

            // Return the raw literals without checking for tautology
            // The ActiveSet::equality_resolution will handle that after normalization
            results.push((i, new_literals, flipped));
        }

        results
    }

    /// Generates all clauses that can be derived from this clause using equality resolution.
    /// This is a convenience method that returns just the normalized clauses.
    pub fn equality_resolutions(&self) -> Vec<Clause> {
        self.find_equality_resolutions()
            .into_iter()
            .map(|(_, literals, _)| Clause::new(literals))
            .filter(|clause| !clause.is_tautology())
            .collect()
    }

    /// Finds all possible equality factorings for this clause.
    /// Returns a vector of (literals, ef_trace) pairs.
    /// The literals are the result of factoring before normalization.
    /// The ef_trace tracks how the literals were transformed.
    pub fn find_equality_factorings(&self) -> Vec<(Vec<Literal>, Vec<EFLiteralTrace>)> {
        let mut results = vec![];

        // The first literal must be positive for equality factoring
        if self.literals.is_empty() || !self.literals[0].positive {
            return results;
        }

        let st_literal = &self.literals[0];

        for (st_forwards, s, t) in st_literal.both_term_pairs() {
            for i in 1..self.literals.len() {
                let uv_literal = &self.literals[i];
                if !uv_literal.positive {
                    continue;
                }

                for (uv_forwards, u, v) in uv_literal.both_term_pairs() {
                    let mut unifier = Unifier::new(3);
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

                    for j in 1..self.literals.len() {
                        if i == j {
                            ef_trace.push(EFLiteralTrace::to_out(u_out, v_out, !uv_forwards));
                        } else {
                            let (new_lit, j_flipped) =
                                unifier.apply_to_literal(Scope::LEFT, &self.literals[j]);
                            let index = literals.len();
                            ef_trace.push(EFLiteralTrace::to_index(index, j_flipped));
                            literals.push(new_lit);
                        }
                    }

                    results.push((literals, ef_trace));
                }
            }
        }

        results
    }

    /// Generates all clauses that can be derived from this clause using equality factoring.
    /// This is a convenience method that returns just the normalized clauses.
    pub fn equality_factorings(&self) -> Vec<Clause> {
        self.find_equality_factorings()
            .into_iter()
            .map(|(literals, _)| Clause::new(literals))
            .filter(|clause| !clause.is_tautology())
            .collect()
    }

    /// Finds all possible function eliminations for this clause.
    /// Returns a vector of (index, arg_index, literals, flipped) tuples.
    /// - index: the literal index where function elimination can be applied
    /// - arg_index: which argument position differs
    /// - literals: the resulting literals after function elimination
    /// - flipped: whether the resulting literal was flipped
    pub fn find_function_eliminations(&self) -> Vec<(usize, usize, Vec<Literal>, bool)> {
        let mut results = vec![];

        for (i, target) in self.literals.iter().enumerate() {
            // Check if we can eliminate the functions from the ith literal.
            if target.positive {
                // Negative literals come before positive ones so we're done
                break;
            }
            if target.left.head != target.right.head {
                continue;
            }
            if target.left.num_args() != target.right.num_args() {
                continue;
            }

            // We can do function elimination when precisely one of the arguments is different.
            let mut different_index = None;
            for (j, arg) in target.left.args.iter().enumerate() {
                if arg != &target.right.args[j] {
                    if different_index.is_some() {
                        different_index = None;
                        break;
                    }
                    different_index = Some(j);
                }
            }

            if let Some(j) = different_index {
                // Looks like we can eliminate the functions from this literal
                let mut literals = self.literals.clone();
                let (new_literal, flipped) = Literal::new_with_flip(
                    false,
                    target.left.args[j].clone(),
                    target.right.args[j].clone(),
                );
                literals[i] = new_literal;
                results.push((i, j, literals, flipped));
            }
        }

        results
    }

    /// Generates all clauses that can be derived from this clause using function elimination.
    /// This is a convenience method that returns just the normalized clauses.
    pub fn function_eliminations(&self) -> Vec<Clause> {
        self.find_function_eliminations()
            .into_iter()
            .map(|(_, _, literals, _)| Clause::new(literals))
            .filter(|clause| !clause.is_tautology())
            .collect()
    }
}
