use serde::{Deserialize, Serialize};
use std::fmt;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::fat_literal::FatLiteral;
use crate::kernel::fat_term::{FatTerm, TypeId, BOOL};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::trace::{ClauseTrace, LiteralTrace};
#[cfg(not(feature = "thin"))]
use crate::proof_step::EFLiteralTrace;

/// Builds a LocalContext from a slice of literals by extracting variable types.
/// This is internal to FatClause construction - reads embedded types from FatTerm.
fn build_context_from_literals(literals: &[FatLiteral]) -> LocalContext {
    let mut var_types: Vec<Option<TypeId>> = vec![];
    for literal in literals {
        for (var_id, type_id) in literal
            .left
            .collect_vars_embedded()
            .into_iter()
            .chain(literal.right.collect_vars_embedded())
        {
            let idx = var_id as usize;
            if idx >= var_types.len() {
                var_types.resize(idx + 1, None);
            }
            var_types[idx] = Some(type_id);
        }
    }
    LocalContext::new(
        var_types
            .into_iter()
            .map(|t| t.unwrap_or_default())
            .collect(),
    )
}

/// Builds a LocalContext from a slice of terms by extracting variable types.
/// This reads embedded types from FatTerm - for FatTerm internal use only.
pub fn build_context_from_terms(terms: &[&FatTerm]) -> LocalContext {
    let mut var_types: Vec<Option<TypeId>> = vec![];
    for term in terms {
        for (var_id, type_id) in term.collect_vars_embedded() {
            let idx = var_id as usize;
            if idx >= var_types.len() {
                var_types.resize(idx + 1, None);
            }
            var_types[idx] = Some(type_id);
        }
    }
    LocalContext::new(
        var_types
            .into_iter()
            .map(|t| t.unwrap_or_default())
            .collect(),
    )
}

/// A clause is a disjunction (an "or") of literals, universally quantified over some variables.
/// We include the types of the universal variables it is quantified over.
/// It cannot contain existential quantifiers.
///
/// Note: The context field is excluded from equality/hash/ordering comparisons.
/// Two clauses with the same literals are considered equal regardless of their contexts.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FatClause {
    pub literals: Vec<FatLiteral>,
    #[serde(default = "LocalContext::empty")]
    context: LocalContext,
}

impl PartialEq for FatClause {
    fn eq(&self, other: &Self) -> bool {
        self.literals == other.literals
    }
}

impl Eq for FatClause {}

impl std::hash::Hash for FatClause {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.literals.hash(state);
    }
}

impl Ord for FatClause {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.literals.cmp(&other.literals)
    }
}

impl PartialOrd for FatClause {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for FatClause {
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

impl FatClause {
    /// Get the local context for this clause.
    /// Returns the context that stores variable types for this clause.
    pub fn get_local_context(&self) -> &LocalContext {
        &self.context
    }

    /// Creates a new normalized clause.
    /// The context parameter is ignored for FatClause but accepted for API compatibility with ThinClause.
    pub fn new(literals: Vec<FatLiteral>, _context: &LocalContext) -> FatClause {
        Self::new_without_context(literals)
    }

    /// Creates a new normalized clause without requiring a context.
    /// This is the original FatClause::new - use this when you don't have a LocalContext.
    pub fn new_without_context(literals: Vec<FatLiteral>) -> FatClause {
        let mut c = FatClause {
            literals,
            context: LocalContext::empty(),
        };
        c.normalize();
        c.context = build_context_from_literals(&c.literals);
        c
    }

    /// Creates a clause from literals without normalizing.
    /// The context is built from the literals.
    /// Use this when you need to skip normalization (e.g., for permutation generation).
    /// The _context parameter is ignored for FatClause (context is built from literals),
    /// but is included for API compatibility with ThinClause.
    pub fn from_literals_unnormalized(
        literals: Vec<FatLiteral>,
        _context: &LocalContext,
    ) -> FatClause {
        let context = build_context_from_literals(&literals);
        FatClause { literals, context }
    }

    /// Sorts literals.
    /// Removes any duplicate or impossible literals.
    /// An empty clause indicates an impossible clause.
    pub fn normalize(&mut self) {
        self.literals.retain(|lit| !lit.is_impossible());
        self.literals.sort();
        self.literals.dedup();
        self.normalize_var_ids();
    }

    /// Normalizes literals into a clause, creating a trace of where each one is sent.
    /// Note that this doesn't flip any literals. It only creates the "Output" and "Impossible"
    /// type traces.
    /// The _context parameter is ignored for FatClause (context is built from literals),
    /// but is included for API compatibility with ThinClause.
    pub fn normalize_with_trace(
        literals: Vec<FatLiteral>,
        _context: &LocalContext,
    ) -> (FatClause, ClauseTrace) {
        let mut trace = vec![LiteralTrace::Impossible; literals.len()];

        // Pair each literal with its initial index.
        let mut indexed_literals: Vec<(FatLiteral, usize)> = literals
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
        let mut var_ids = vec![];
        for i in 0..output_literals.len() {
            if output_literals[i].normalize_var_ids(&mut var_ids) {
                // We flipped literal i. Update the trace.
                for t in &mut trace {
                    if let LiteralTrace::Output { index, flipped } = t {
                        if *index == i {
                            *flipped = !*flipped;
                        }
                    }
                }
            }
        }
        let context = build_context_from_literals(&output_literals);
        let c = FatClause {
            literals: output_literals,
            context,
        };
        (c, ClauseTrace::new(trace))
    }

    pub fn validate(&self) {
        // Check that the literals are sorted
        for i in 0..self.literals.len() {
            if i > 0 && self.literals[i - 1] > self.literals[i] {
                panic!("Clause literals are not sorted: {}", self);
            }
        }
        for literal in &self.literals {
            if literal.is_tautology() {
                panic!("Clause contains tautology literal: {}", self);
            }
            if literal.is_impossible() {
                panic!("Clause contains impossible literal: {}", self);
            }
            if !literal.is_normalized() {
                panic!("Clause {} has bad literal {}", self, literal);
            }
        }
        let mut next_var_id = 0;
        for atom in self.iter_atoms() {
            if let Atom::Variable(id) = atom {
                if *id > next_var_id {
                    panic!(
                        "Clause {} skips variable ids: expected <= {}, found {}",
                        self, next_var_id, id
                    );
                }
                if *id == next_var_id {
                    next_var_id += 1;
                }
            }
        }
    }

    /// Creates a new clause and a new trace, given a list of literals and a
    /// trace of how they were created.
    /// The _context parameter is ignored for FatClause (context is built from literals),
    /// but is included for API compatibility with ThinClause.
    pub fn new_with_trace(
        literals: Vec<FatLiteral>,
        mut trace: ClauseTrace,
        _context: &LocalContext,
    ) -> (FatClause, ClauseTrace) {
        let (c, incremental_trace) =
            FatClause::normalize_with_trace(literals, &LocalContext::empty());
        trace.compose(&incremental_trace);
        (c, trace)
    }

    /// Creates a new clause. If a trace is provided, we compose the traces.
    /// The base_trace should be applicable to the provided literals.
    /// The _context parameter is ignored for FatClause (context is built from literals),
    /// but is included for API compatibility with ThinClause.
    pub fn new_composing_traces(
        literals: Vec<FatLiteral>,
        base_trace: Option<ClauseTrace>,
        incremental_trace: &ClauseTrace,
        _context: &LocalContext,
    ) -> (FatClause, Option<ClauseTrace>) {
        let Some(mut base_trace) = base_trace else {
            return (FatClause::new_without_context(literals), None);
        };
        base_trace.compose(incremental_trace);
        let (c, trace) = FatClause::new_with_trace(literals, base_trace, &LocalContext::empty());
        (c, Some(trace))
    }

    /// Creates a clause from a single literal with trace.
    /// The _context parameter is ignored for FatClause (context is built from literals),
    /// but is included for API compatibility with ThinClause.
    pub fn from_literal_traced(
        literal: FatLiteral,
        flipped: bool,
        _context: &LocalContext,
    ) -> (FatClause, ClauseTrace) {
        FatClause::new_with_trace(
            vec![literal],
            ClauseTrace::new(vec![LiteralTrace::Output { index: 0, flipped }]),
            &LocalContext::empty(),
        )
    }

    /// Normalizes the variable IDs in the literals.
    /// This may flip literals, so keep in mind it will break any trace.
    pub fn normalize_var_ids(&mut self) {
        let mut var_ids = vec![];
        for literal in &mut self.literals {
            // Note: this doesn't update the trace.
            literal.normalize_var_ids(&mut var_ids);
        }
        self.context = build_context_from_literals(&self.literals);
    }

    /// Normalizes the variable IDs in the literals so that they are ascending,
    /// but does not flip any literals if this then disorders those literals.
    /// This may produce non-normalized literals.
    pub fn normalize_var_ids_no_flip(&mut self) {
        let mut var_ids = vec![];
        for literal in &mut self.literals {
            literal.left.normalize_var_ids(&mut var_ids);
            literal.right.normalize_var_ids(&mut var_ids);
        }
        self.context = build_context_from_literals(&self.literals);
    }

    /// An unsatisfiable clause. Like a lone "false".
    pub fn impossible() -> FatClause {
        FatClause::new_without_context(vec![])
    }

    /// Parse a clause from a string representation.
    /// The _context parameter is ignored for FatClause (context is built from literals),
    /// but is included for API compatibility with ThinClause.
    pub fn parse(s: &str, _context: &LocalContext) -> FatClause {
        FatClause::new_without_context(
            s.split(" or ")
                .map(|x| FatLiteral::parse(x))
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

    /// Iterates over all atoms in the clause (from all literals in order)
    pub fn iter_atoms(&self) -> Box<dyn Iterator<Item = &Atom> + '_> {
        Box::new(
            self.literals
                .iter()
                .flat_map(|literal| literal.iter_atoms()),
        )
    }

    pub fn has_any_variable(&self) -> bool {
        self.literals.iter().any(|x| x.has_any_variable())
    }

    pub fn has_any_applied_variable(&self) -> bool {
        self.literals.iter().any(|x| x.has_any_applied_variable())
    }

    pub fn has_synthetic(&self) -> bool {
        self.literals.iter().any(|x| x.has_synthetic())
    }

    pub fn has_scoped_constant(&self) -> bool {
        self.literals.iter().any(|x| x.has_scoped_constant())
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
    pub fn contains(&self, other: &FatClause) -> bool {
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

    /// Renumbers synthetic atoms from the provided list into the invalid range.
    /// This does renormalize, so it could reorder literals and renumber variables.
    pub fn invalidate_synthetics(&self, from: &[AtomId]) -> FatClause {
        let new_literals: Vec<FatLiteral> = self
            .literals
            .iter()
            .map(|lit| lit.invalidate_synthetics(from))
            .collect();
        FatClause::new_without_context(new_literals)
    }

    /// Replace the first `num_to_replace` variables with invalid synthetic atoms, adjusting
    /// the subsequent variable ids accordingly.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> FatClause {
        let new_literals: Vec<FatLiteral> = self
            .literals
            .iter()
            .map(|lit| lit.instantiate_invalid_synthetics(num_to_replace))
            .collect();
        FatClause::new_without_context(new_literals)
    }

    // The inference methods (find_equality_resolutions, find_equality_factorings, etc.)
    // are in the inference module and work with the Clause/Literal/Term aliases.
    // When not using the thin feature, FatClause IS the Clause alias, so these work.
    // When using the thin feature, use the inference module directly with ThinClause.
    #[cfg(not(feature = "thin"))]
    /// Finds all possible equality resolutions for this clause.
    /// Returns a vector of tuples containing:
    /// - The index of the literal that was resolved
    /// - The resulting literals after applying the unifier
    /// - The flipped flags for each literal
    /// Returns (index, new_literals, flipped, output_context) for each possible equality resolution.
    /// The output_context contains the types of variables in the resulting literals.
    pub fn find_equality_resolutions(
        &self,
        kernel_context: &KernelContext,
    ) -> Vec<(usize, Vec<FatLiteral>, Vec<bool>, LocalContext)> {
        crate::kernel::inference::find_equality_resolutions(self, kernel_context)
    }

    #[cfg(not(feature = "thin"))]
    /// Generates all clauses that can be derived from this clause using equality resolution.
    /// This is a convenience method that returns just the normalized clauses.
    pub fn equality_resolutions(&self, kernel_context: &KernelContext) -> Vec<FatClause> {
        crate::kernel::inference::equality_resolutions(self, kernel_context)
    }

    #[cfg(not(feature = "thin"))]
    /// Finds all possible equality factorings for this clause.
    /// Returns a vector of (literals, ef_trace) pairs.
    /// The literals are the result of factoring before normalization.
    /// The ef_trace tracks how the literals were transformed.
    pub fn find_equality_factorings(
        &self,
        kernel_context: &KernelContext,
    ) -> Vec<(Vec<FatLiteral>, Vec<EFLiteralTrace>)> {
        crate::kernel::inference::find_equality_factorings(self, kernel_context)
    }

    #[cfg(not(feature = "thin"))]
    /// Generates all clauses that can be derived from this clause using equality factoring.
    /// This is a convenience method that returns just the normalized clauses.
    pub fn equality_factorings(&self, kernel_context: &KernelContext) -> Vec<FatClause> {
        crate::kernel::inference::equality_factorings(
            self,
            self.get_local_context(),
            kernel_context,
        )
    }

    /// Finds all possible injectivity applications for this clause.
    /// Returns a vector of (index, arg_index, literals, flipped) tuples.
    /// - index: the literal index where injectivity can be applied
    /// - arg_index: which argument position differs
    /// - literals: the resulting literals after applying injectivity
    /// - flipped: whether the resulting literal was flipped
    pub fn find_injectivities(&self) -> Vec<(usize, usize, Vec<FatLiteral>, bool)> {
        let mut results = vec![];

        for (i, target) in self.literals.iter().enumerate() {
            // Check if we can apply injectivity to the ith literal.
            if target.positive {
                // Negative literals come before positive ones so we're done
                break;
            }
            if target.left.get_head_atom() != target.right.get_head_atom() {
                continue;
            }
            if target.left.num_args() != target.right.num_args() {
                continue;
            }

            // We can do function elimination when precisely one of the arguments is different.
            let mut different_index = None;
            for (j, arg) in target.left.args().iter().enumerate() {
                if arg != &target.right.args()[j] {
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
                let (new_literal, flipped) = FatLiteral::new_with_flip(
                    false,
                    target.left.args()[j].clone(),
                    target.right.args()[j].clone(),
                );
                literals[i] = new_literal;
                results.push((i, j, literals, flipped));
            }
        }

        results
    }

    /// Generates all clauses that can be derived from this clause using injectivity.
    /// This is a convenience method that returns just the normalized clauses.
    pub fn injectivities(&self) -> Vec<FatClause> {
        self.find_injectivities()
            .into_iter()
            .map(|(_, _, literals, _)| FatClause::new_without_context(literals))
            .filter(|clause| !clause.is_tautology())
            .collect()
    }

    /// Generates all clauses that can be derived from this clause using boolean reduction.
    /// Boolean reduction is replacing a boolean equality with a disjunction that it implies.
    ///
    /// Returns a vector of (index, resulting_literals) pairs.
    /// The index describes the index of a literal that got replaced by two literals.
    /// We always replace a (left ~ right) at position i with ~left at i and ~right at i+1.
    pub fn find_boolean_reductions(
        &self,
        kernel_context: &KernelContext,
    ) -> Vec<(usize, Vec<FatLiteral>)> {
        let mut answer = vec![];

        for i in 0..self.literals.len() {
            let literal = &self.literals[i];
            if literal
                .left
                .get_term_type_with_context(&self.context, kernel_context)
                != BOOL
            {
                continue;
            }
            if literal.right.is_true() {
                continue;
            }
            // We make two copies since there are two ways to do it
            let mut first = self.literals[..i].to_vec();
            let mut second = self.literals[..i].to_vec();
            if literal.positive {
                first.push(FatLiteral::positive(literal.left.clone()));
                first.push(FatLiteral::negative(literal.right.clone()));
                second.push(FatLiteral::negative(literal.left.clone()));
                second.push(FatLiteral::positive(literal.right.clone()));
            } else {
                first.push(FatLiteral::negative(literal.left.clone()));
                first.push(FatLiteral::negative(literal.right.clone()));
                second.push(FatLiteral::positive(literal.left.clone()));
                second.push(FatLiteral::positive(literal.right.clone()));
            }
            first.extend_from_slice(&self.literals[i + 1..]);
            second.extend_from_slice(&self.literals[i + 1..]);
            answer.push((i, first));
            answer.push((i, second));
        }
        answer
    }

    /// Generates all clauses that can be derived from this clause using boolean reduction.
    /// This is a convenience method that returns just the normalized clauses.
    pub fn boolean_reductions(&self, kernel_context: &KernelContext) -> Vec<FatClause> {
        let mut answer = vec![];
        for (_, literals) in self.find_boolean_reductions(kernel_context) {
            let clause = FatClause::new_without_context(literals);
            answer.push(clause);
        }
        answer
    }

    /// Finds if extensionality can be applied to this clause.
    /// Returns the resulting literals if extensionality applies.
    /// Only works on single-literal clauses.
    pub fn find_extensionality(&self, kernel_context: &KernelContext) -> Option<Vec<FatLiteral>> {
        // Extensionality only works on single-literal clauses
        if self.literals.len() != 1 {
            return None;
        }
        let literal = &self.literals[0];

        // Extensionality only applies to positive equality literals
        if !literal.positive {
            return None;
        }

        // Check if this is f(a, b, c, x1, x2, ..., xn) = g(x1, x2, ..., xn)
        let (longer, shorter) = if literal.left.args().len() >= literal.right.args().len() {
            (&literal.left, &literal.right)
        } else {
            (&literal.right, &literal.left)
        };

        // Both sides must be function applications
        if longer.args().is_empty() || shorter.args().is_empty() {
            return None;
        }

        // Functions must be different
        if longer.get_head_atom() == shorter.get_head_atom() {
            return None;
        }

        // The extra args on the longer side must have no variables
        let diff = longer.args().len() - shorter.args().len();
        if longer.args()[0..diff].iter().any(|arg| arg.is_variable()) {
            return None;
        }

        // Remaining arguments must be the same
        if longer.args()[diff..] != *shorter.args() {
            return None;
        }

        // Check that variables are distinct (0, 1, 2, ... in normalized form)
        for (i, arg) in shorter.args().iter().enumerate() {
            let Atom::Variable(id) = arg.get_head_atom() else {
                return None;
            };
            if *id != i as AtomId {
                return None;
            }
        }

        // Create the new literal.
        // We need to take the type from the head of the shorter term.
        let new_left = shorter.get_head_term();
        let new_right = FatTerm::new(
            new_left.get_term_type_with_context(&self.context, kernel_context),
            longer.get_head_type_with_context(&self.context, kernel_context),
            *longer.get_head_atom(),
            longer.args()[0..diff].to_vec(),
        );
        let new_literal = FatLiteral::new(true, new_left, new_right);
        Some(vec![new_literal])
    }

    /// Extracts the polarity of each literal and returns a new clause with sorted positive literals
    /// along with a vector of polarities that correspond to each literal in the sorted order.
    pub fn extract_polarity(&self) -> (FatClause, Vec<bool>) {
        let mut literal_polarity_pairs: Vec<(FatLiteral, bool)> = self
            .literals
            .iter()
            .map(|lit| lit.extract_polarity())
            .collect();

        // Sort the pairs by the positive literal
        literal_polarity_pairs.sort_by(|a, b| a.0.cmp(&b.0));

        let (literals, polarities): (Vec<FatLiteral>, Vec<bool>) =
            literal_polarity_pairs.into_iter().unzip();

        let context = build_context_from_literals(&literals);
        (FatClause { literals, context }, polarities)
    }
}

#[cfg(test)]
fn check(s: &str) {
    use crate::kernel::kernel_context::KernelContext;

    let literals: Vec<FatLiteral> = s
        .split(" or ")
        .map(|x| FatLiteral::parse(x))
        .collect::<Vec<_>>();
    let clause = FatClause::new_without_context(literals.clone());
    let (alt_clause, trace) =
        FatClause::normalize_with_trace(literals.clone(), &LocalContext::empty());
    assert_eq!(clause, alt_clause);

    let kernel_context = KernelContext::test_with_constants(10, 10);
    let literals_context = build_context_from_literals(&literals);
    clause.validate();
    trace.validate(&literals, &literals_context, &clause, &kernel_context);
}

#[test]
fn test_easy_clause_normalization() {
    check("c0 or c1");
}

#[test]
fn test_hard_clause_normalization() {
    check("not x0(x2) or c0(x0, x1, x2) or x1 = x2");
}
