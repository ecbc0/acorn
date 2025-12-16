use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::Term;
use crate::kernel::trace::{ClauseTrace, LiteralTrace};

/// A Clause represents a disjunction (an "or") of literals.
/// Type information is stored separately in the TypeStore and SymbolTable,
/// along with a Context that tracks the types of variables in the clause.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Clause {
    pub literals: Vec<Literal>,
    pub context: LocalContext,
}

impl Clause {
    /// Get the local context for this clause.
    /// This returns the context that stores variable types for this clause.
    pub fn get_local_context(&self) -> &LocalContext {
        &self.context
    }

    /// Creates a new normalized clause.
    pub fn new(literals: Vec<Literal>, context: &LocalContext) -> Clause {
        // Debug: validate that all variables in literals have types in context
        #[cfg(debug_assertions)]
        for (i, lit) in literals.iter().enumerate() {
            for atom in lit.iter_atoms() {
                if let crate::kernel::atom::Atom::FreeVariable(var_id) = atom {
                    if context.get_var_type(*var_id as usize).is_none() {
                        panic!(
                            "Clause::new: literal {} has variable x{} but context has no type for it. Context len: {}",
                            i, var_id, context.len()
                        );
                    }
                }
            }
        }
        let mut c = Clause {
            literals,
            context: context.clone(),
        };
        c.normalize();
        c
    }

    /// Normalizes literals into a clause, creating a trace of where each one is sent.
    /// Tracks flips that occur during variable ID normalization.
    pub fn normalize_with_trace(
        literals: Vec<Literal>,
        context: &LocalContext,
    ) -> (Clause, ClauseTrace) {
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

        // Normalize variable IDs and track flips, rebuilding the context.
        // var_ids will contain the original variable IDs in their new order.
        let mut var_ids = vec![];
        for i in 0..output_literals.len() {
            if output_literals[i].normalize_var_ids_into(&mut var_ids) {
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

        let clause = Clause {
            literals: output_literals,
            context: context.remap(&var_ids),
        };
        (clause, ClauseTrace::new(trace))
    }

    /// Creates a new clause and a new trace, given a list of literals and a
    /// trace of how they were created.
    pub fn new_with_trace(
        literals: Vec<Literal>,
        mut trace: ClauseTrace,
        context: &LocalContext,
    ) -> (Clause, ClauseTrace) {
        let (c, incremental_trace) = Clause::normalize_with_trace(literals, context);
        trace.compose(&incremental_trace);
        (c, trace)
    }

    /// Creates a new clause. If a trace is provided, we compose the traces.
    /// The base_trace should be applicable to the provided literals.
    pub fn new_composing_traces(
        literals: Vec<Literal>,
        base_trace: Option<ClauseTrace>,
        incremental_trace: &ClauseTrace,
        context: &LocalContext,
    ) -> (Clause, Option<ClauseTrace>) {
        let Some(mut base_trace) = base_trace else {
            return (Clause::new(literals, context), None);
        };
        base_trace.compose(incremental_trace);
        let (c, trace) = Clause::new_with_trace(literals, base_trace, context);
        (c, Some(trace))
    }

    /// Create a clause from a single literal with trace.
    pub fn from_literal_traced(
        literal: Literal,
        flipped: bool,
        context: &LocalContext,
    ) -> (Clause, ClauseTrace) {
        Clause::new_with_trace(
            vec![literal],
            ClauseTrace::new(vec![LiteralTrace::Output { index: 0, flipped }]),
            context,
        )
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

    /// Normalizes the variable IDs in the literals.
    /// This may flip literals, so keep in mind it will break any trace.
    /// Also rebuilds the context to match the renumbered variables.
    pub fn normalize_var_ids(&mut self) {
        let mut var_ids = vec![];
        let input_context = self.context.clone();
        for literal in &mut self.literals {
            literal.normalize_var_ids_into(&mut var_ids);
        }
        self.context = input_context.remap(&var_ids);
    }

    /// Create an impossible clause (empty clause, represents false).
    pub fn impossible() -> Clause {
        Clause {
            literals: vec![],
            context: LocalContext::empty(),
        }
    }

    /// Get the number of literals in this clause.
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    /// Check if this is an empty (impossible) clause.
    pub fn is_impossible(&self) -> bool {
        self.literals.is_empty()
    }

    /// Check if this clause is a tautology (contains a tautological literal or contradictory pair).
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

    /// Check if this clause contains any variables.
    pub fn has_any_variable(&self) -> bool {
        self.literals.iter().any(|x| x.has_any_variable())
    }

    /// Check if this clause contains any local constants.
    pub fn has_scoped_constant(&self) -> bool {
        self.literals.iter().any(|x| x.has_scoped_constant())
    }

    /// Check if this clause contains any synthetic atoms.
    pub fn has_synthetic(&self) -> bool {
        self.literals.iter().any(|x| x.has_synthetic())
    }

    /// Count the total number of atoms across all literals.
    pub fn atom_count(&self) -> u32 {
        self.literals.iter().map(|x| x.atom_count()).sum()
    }

    /// Get the least unused variable index.
    pub fn least_unused_variable(&self) -> AtomId {
        self.literals
            .iter()
            .map(|x| x.least_unused_variable())
            .max()
            .unwrap_or(0)
    }

    /// Iterate over all atoms in all literals.
    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom> + '_ {
        self.literals
            .iter()
            .flat_map(|literal| literal.iter_atoms())
    }

    /// Check if this clause contains all literals from another clause.
    pub fn contains(&self, other: &Clause) -> bool {
        for literal in &other.literals {
            if !self.literals.iter().any(|x| x == literal) {
                return false;
            }
        }
        true
    }

    /// Check if any top level term has the given atom as its head.
    pub fn has_head(&self, atom: &Atom) -> bool {
        for literal in &self.literals {
            if literal.left.get_head_atom() == atom || literal.right.get_head_atom() == atom {
                return true;
            }
        }
        false
    }

    /// Normalize variable IDs without flipping literals.
    /// Also rebuilds the context to match the renumbered variables.
    pub fn normalize_var_ids_no_flip(&mut self) {
        let mut var_ids = vec![];
        let input_context = self.context.clone();
        for literal in &mut self.literals {
            literal.left.normalize_var_ids_into(&mut var_ids);
            literal.right.normalize_var_ids_into(&mut var_ids);
        }
        self.context = input_context.remap(&var_ids);
    }

    /// Create a clause from literals without normalizing.
    pub fn from_literals_unnormalized(literals: Vec<Literal>, context: &LocalContext) -> Clause {
        // Debug: validate that all variables in literals have types in context
        #[cfg(debug_assertions)]
        for (i, lit) in literals.iter().enumerate() {
            for atom in lit.iter_atoms() {
                if let crate::kernel::atom::Atom::FreeVariable(var_id) = atom {
                    if context.get_var_type(*var_id as usize).is_none() {
                        panic!(
                            "Clause::from_literals_unnormalized: literal {} has variable x{} but context has no type for it. Context len: {}",
                            i, var_id, context.len()
                        );
                    }
                }
            }
        }
        Clause {
            literals,
            context: context.clone(),
        }
    }

    /// Validate that all literals have consistent types.
    ///
    /// This validation only runs in test builds or when the "validate" feature is enabled.
    /// It's skipped in production for performance reasons.
    pub fn validate(&self, kernel_context: &KernelContext) {
        #[cfg(not(any(test, feature = "validate")))]
        {
            let _ = kernel_context;
            return;
        }

        #[cfg(any(test, feature = "validate"))]
        {
            // Check that no variable has the Empty type
            if let Some(var_id) = self.context.find_empty_type() {
                panic!(
                    "Clause validation failed: variable x{} has Empty type. Clause: {}",
                    var_id, self
                );
            }

            for literal in &self.literals {
                literal.validate_type(&self.context, kernel_context);
            }
        }
    }

    /// Renumbers synthetic atoms from the provided list into the invalid range.
    pub fn invalidate_synthetics(&self, from: &[AtomId]) -> Clause {
        let new_literals: Vec<Literal> = self
            .literals
            .iter()
            .map(|lit| lit.invalidate_synthetics(from))
            .collect();
        Clause::new(new_literals, &self.context).canonicalize()
    }

    /// Replace the first `num_to_replace` variables with invalid synthetic atoms.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> Clause {
        let new_literals: Vec<Literal> = self
            .literals
            .iter()
            .map(|lit| lit.instantiate_invalid_synthetics(num_to_replace))
            .collect();
        // The context needs to be adjusted - the first num_to_replace var types are removed
        let new_types: Vec<_> = self
            .context
            .get_var_types()
            .iter()
            .skip(num_to_replace)
            .cloned()
            .collect();
        let new_context = LocalContext::from_types(new_types);
        Clause::new(new_literals, &new_context).canonicalize()
    }

    /// Returns a canonical form of this clause with literals in deterministic order.
    /// This is used for SyntheticKey matching where we need clauses to match
    /// regardless of variable naming in the source.
    fn canonicalize(&self) -> Clause {
        // The clause has already been through Clause::new, so variables are renumbered.
        // But literals might be in different order if the stable sort didn't break ties.
        // Re-sort using total ordering now that variables are normalized.
        let mut literals = self.literals.clone();
        literals.sort();

        // Now renumber variables again based on the new literal order
        let mut var_ids = vec![];
        for lit in &mut literals {
            lit.normalize_var_ids_into(&mut var_ids);
        }

        Clause {
            literals,
            context: self.context.remap(&var_ids),
        }
    }

    /// Extracts the polarity from all literals.
    /// Returns a clause with all positive literals and a vector of the original polarities.
    pub fn extract_polarity(&self) -> (Clause, Vec<bool>) {
        let mut polarities = Vec::new();
        let mut new_literals = Vec::new();
        for literal in &self.literals {
            let (pos_lit, polarity) = literal.extract_polarity();
            new_literals.push(pos_lit);
            polarities.push(polarity);
        }
        (
            Clause::from_literals_unnormalized(new_literals, &self.context),
            polarities,
        )
    }

    /// Finds all possible injectivity applications for this clause.
    /// Returns a vector of (index, arg_index, literals, flipped) tuples.
    /// - index: the literal index where injectivity can be applied
    /// - arg_index: which argument position differs
    /// - literals: the resulting literals after applying injectivity
    /// - flipped: whether the resulting literal was flipped
    pub fn find_injectivities(&self) -> Vec<(usize, usize, Vec<Literal>, bool)> {
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
            let left_args = target.left.args();
            let right_args = target.right.args();
            let mut different_index = None;
            for (j, arg) in left_args.iter().enumerate() {
                if arg != &right_args[j] {
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
                let (new_literal, flipped) =
                    Literal::new_with_flip(false, left_args[j].clone(), right_args[j].clone());
                literals[i] = new_literal;
                results.push((i, j, literals, flipped));
            }
        }

        results
    }

    /// Generates all clauses that can be derived from this clause using injectivity.
    /// This is a convenience method that returns just the normalized clauses.
    pub fn injectivities(&self) -> Vec<Clause> {
        self.find_injectivities()
            .into_iter()
            .map(|(_, _, literals, _)| Clause::new(literals, &self.context))
            .filter(|clause| !clause.is_tautology())
            .collect()
    }

    /// Finds if extensionality can be applied to this clause.
    /// Returns the resulting literals if extensionality applies.
    /// Only works on single-literal clauses.
    ///
    /// Lambda-native: We peel arguments from the right only as long as they are
    /// distinct free variables. This allows extensionality to work when leading
    /// arguments are ground constants (like type arguments).
    ///
    /// Example: f(T, x, y) = g(T, x, y) where T is ground, x and y are free vars
    /// → Peels y then x, stops at T → Result: f(T) = g(T)
    pub fn find_extensionality(&self, kernel_context: &KernelContext) -> Option<Vec<Literal>> {
        // Extensionality only works on single-literal clauses
        if self.literals.len() != 1 {
            return None;
        }
        let literal = &self.literals[0];

        // Extensionality only applies to positive equality literals
        if !literal.positive {
            return None;
        }

        // Check if this is f(..., x1, x2, ..., xn) = g(..., x1, x2, ..., xn)
        // where the trailing args match and can be peeled via extensionality.
        let (longer, shorter) = if literal.left.num_args() >= literal.right.num_args() {
            (&literal.left, &literal.right)
        } else {
            (&literal.right, &literal.left)
        };

        // Both sides must be function applications
        if longer.num_args() == 0 || shorter.num_args() == 0 {
            return None;
        }

        // Functions must be different
        if longer.get_head_atom() == shorter.get_head_atom() {
            return None;
        }

        // Heads must not be variables
        if longer.get_head_atom().is_variable() || shorter.get_head_atom().is_variable() {
            return None;
        }

        let longer_args = longer.args();
        let shorter_args = shorter.args();

        // Find the longest matching suffix between longer_args and shorter_args.
        // We compare from the right: longer_args[len-1] vs shorter_args[len-1], etc.
        let mut matching_suffix_len = 0;
        let longer_len = longer_args.len();
        let shorter_len = shorter_args.len();
        while matching_suffix_len < shorter_len {
            let longer_idx = longer_len - 1 - matching_suffix_len;
            let shorter_idx = shorter_len - 1 - matching_suffix_len;
            if longer_args[longer_idx] != shorter_args[shorter_idx] {
                break;
            }
            matching_suffix_len += 1;
        }

        if matching_suffix_len == 0 {
            return None; // No matching suffix at all
        }

        // Find the longest right-suffix of matching args that are distinct free variables.
        // We peel from the right, stopping when we hit a non-variable or a duplicate.
        let mut peel_count = 0;
        let mut peeled_vars: HashSet<AtomId> = HashSet::new();

        for i in 0..matching_suffix_len {
            // Index from the right
            let shorter_idx = shorter_len - 1 - i;
            let arg = &shorter_args[shorter_idx];
            match arg.atomic_variable() {
                Some(var_id) => {
                    // Check this var is distinct from vars we're already peeling
                    if peeled_vars.contains(&var_id) {
                        break; // Duplicate var, stop peeling
                    }

                    // Check var is not in the prefix (non-peeled args) on either side
                    let longer_prefix_end = longer_len - peel_count;
                    let shorter_prefix_end = shorter_len - peel_count;
                    let mut var_in_prefix = false;

                    // Check longer's prefix (all args except peeled suffix)
                    for j in 0..longer_prefix_end {
                        if j < longer_len - matching_suffix_len || j < longer_len - 1 - i {
                            if longer_args[j].has_variable(var_id) {
                                var_in_prefix = true;
                                break;
                            }
                        }
                    }

                    // Also check shorter's prefix
                    if !var_in_prefix {
                        for j in 0..shorter_prefix_end {
                            if j < shorter_idx {
                                if shorter_args[j].has_variable(var_id) {
                                    var_in_prefix = true;
                                    break;
                                }
                            }
                        }
                    }

                    if var_in_prefix {
                        break; // Var appears in prefix, stop peeling
                    }

                    peeled_vars.insert(var_id);
                    peel_count += 1;
                }
                None => break, // Not a variable, stop peeling
            }
        }

        if peel_count == 0 {
            return None; // Can't peel anything
        }

        // Build the new terms by removing only peel_count args from the right
        let new_longer_arg_count = longer_len - peel_count;
        let new_shorter_arg_count = shorter_len - peel_count;

        let new_longer = if new_longer_arg_count == 0 {
            longer.get_head_term()
        } else {
            let args: Vec<_> = longer_args[..new_longer_arg_count]
                .iter()
                .map(|a| a.to_owned())
                .collect();
            Term::new(*longer.get_head_atom(), args)
        };

        let new_shorter = if new_shorter_arg_count == 0 {
            shorter.get_head_term()
        } else {
            let args: Vec<_> = shorter_args[..new_shorter_arg_count]
                .iter()
                .map(|a| a.to_owned())
                .collect();
            Term::new(*shorter.get_head_atom(), args)
        };

        // Check the types are compatible
        let longer_type = new_longer.get_type_with_context(&self.context, kernel_context);
        let shorter_type = new_shorter.get_type_with_context(&self.context, kernel_context);
        if longer_type != shorter_type {
            return None;
        }

        let (new_lit, _) = Literal::new_with_flip(true, new_longer, new_shorter);
        Some(vec![new_lit])
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
    ) -> Vec<(usize, Vec<Literal>)> {
        let bool_type = Term::bool_type();

        let mut answer = vec![];

        for i in 0..self.literals.len() {
            let literal = &self.literals[i];
            if literal
                .left
                .get_type_with_context(&self.context, kernel_context)
                != bool_type
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
                first.push(Literal::positive(literal.left.clone()));
                first.push(Literal::negative(literal.right.clone()));
                second.push(Literal::negative(literal.left.clone()));
                second.push(Literal::positive(literal.right.clone()));
            } else {
                first.push(Literal::negative(literal.left.clone()));
                first.push(Literal::negative(literal.right.clone()));
                second.push(Literal::positive(literal.left.clone()));
                second.push(Literal::positive(literal.right.clone()));
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
    pub fn boolean_reductions(&self, kernel_context: &KernelContext) -> Vec<Clause> {
        let mut answer = vec![];
        for (_, literals) in self.find_boolean_reductions(kernel_context) {
            let clause = Clause::new(literals, &self.context);
            answer.push(clause);
        }
        answer
    }
}

impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.literals.is_empty() {
            write!(f, "<empty>")
        } else {
            for (i, literal) in self.literals.iter().enumerate() {
                if i > 0 {
                    write!(f, " or ")?;
                }
                write!(f, "{}", literal)?;
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::atom::Atom;
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::literal::Literal;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::term::Term;
    use crate::kernel::types::GroundTypeId;

    /// Test that extensionality doesn't match clauses without function applications.
    /// This prevents infinite recursion when extensionality produces the same clause.
    #[test]
    fn test_extensionality_rejects_atomic_terms() {
        let kernel_context = KernelContext::new();

        // Create a clause like "g0 = x0" (global constant equals variable)
        let g0 = Term::atom(Atom::Symbol(Symbol::GlobalConstant(0)));
        let x0 = Term::atom(Atom::FreeVariable(0));
        let literal = Literal::equals(g0, x0);

        let some_type = Term::ground_type(GroundTypeId::new(2));
        let context = LocalContext::from_types(vec![some_type]);
        let clause = Clause::from_literals_unnormalized(vec![literal], &context);

        // Extensionality should not match this clause since both terms are atomic
        assert!(
            clause.find_extensionality(&kernel_context).is_none(),
            "Extensionality should not match atomic terms"
        );
    }

    /// Test that extensionality doesn't match clauses where functions are the same.
    #[test]
    fn test_extensionality_rejects_same_function() {
        let kernel_context = KernelContext::new();

        // Create a clause like "f(x0) = f(x0)" (same function on both sides)
        let x0 = Term::atom(Atom::FreeVariable(0));
        let f_x0 = Term::new(Atom::Symbol(Symbol::GlobalConstant(0)), vec![x0.clone()]);
        let literal = Literal::equals(f_x0.clone(), f_x0);

        let some_type = Term::ground_type(GroundTypeId::new(2));
        let context = LocalContext::from_types(vec![some_type]);
        let clause = Clause::from_literals_unnormalized(vec![literal], &context);

        // Extensionality should not match this clause since both sides use the same function
        assert!(
            clause.find_extensionality(&kernel_context).is_none(),
            "Extensionality should not match when functions are the same"
        );
    }

    /// Test that extensionality works with ground prefix (like type arguments).
    /// g0(c0, x) = g1(c0, x) where c0 is ground constant, x is free var → g0(c0) = g1(c0)
    #[test]
    fn test_extensionality_with_ground_prefix() {
        let mut kctx = KernelContext::new();
        // c0 is a ground constant, g0 and g1 are functions that take Bool, Bool -> Bool
        kctx.add_constant("c0", "Bool")
            .add_constant("g0", "Bool -> Bool -> Bool")
            .add_constant("g1", "Bool -> Bool -> Bool");

        // Create clause: g0(c0, x0) = g1(c0, x0)
        let clause = kctx.make_clause("g0(c0, x0) = g1(c0, x0)", &["Bool"]);

        // Extensionality should work, peeling x0 but keeping c0
        let result = clause.find_extensionality(&kctx);
        assert!(
            result.is_some(),
            "Extensionality should work with ground prefix"
        );

        // Result should be g0(c0) = g1(c0)
        let result_lits = result.unwrap();
        assert_eq!(result_lits.len(), 1);
        let result_lit = &result_lits[0];
        // Both sides should have 1 argument (c0)
        assert_eq!(result_lit.left.num_args(), 1);
        assert_eq!(result_lit.right.num_args(), 1);
    }

    /// Test that extensionality rejects duplicate variables.
    /// g0(x, x) = g1(x, x) must NOT derive g0 = g1.
    #[test]
    fn test_extensionality_rejects_duplicate_variables() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("g0", "Bool -> Bool -> Bool")
            .add_constant("g1", "Bool -> Bool -> Bool");

        // Create clause: g0(x0, x0) = g1(x0, x0) using x0 for both positions
        let clause = kctx.make_clause("g0(x0, x0) = g1(x0, x0)", &["Bool"]);

        // Extensionality should NOT fully peel because x0 appears twice
        let result = clause.find_extensionality(&kctx);

        // If extensionality applies, verify it doesn't peel down to g0 = g1
        if let Some(result_lits) = result {
            let result_lit = &result_lits[0];
            // Should NOT be g0 = g1 (both with 0 args)
            assert!(
                result_lit.left.num_args() > 0 || result_lit.right.num_args() > 0,
                "Extensionality should not derive g0 = g1 from g0(x, x) = g1(x, x)"
            );
        }
        // If it returns None, that's also acceptable (conservative behavior)
    }

    /// Test that normalize_with_trace correctly preserves variable types when
    /// literals are reordered during sorting. This reproduces a bug where
    /// variable types were getting shuffled incorrectly.
    #[test]
    fn test_normalize_with_trace_preserves_types() {
        // Create a clause with mixed types:
        // not f(x0, x1, x2) or x2
        // where x0: Foo, x1: Foo, x2: Bool
        //
        // After sorting, the literals may be reordered. The variable renumbering
        // should correctly track which type belongs to which new variable ID.

        let type_foo = Term::ground_type(GroundTypeId::new(2)); // Some non-Bool type
        let type_bool = Term::ground_type(GroundTypeId::new(1)); // Bool

        // x0 and x1 are Foo, x2 is Bool
        let x0 = Term::atom(Atom::FreeVariable(0));
        let x1 = Term::atom(Atom::FreeVariable(1));
        let x2 = Term::atom(Atom::FreeVariable(2));

        // Create f(x0, x1, x2) - a function application
        let f_args = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x0.clone(), x1.clone(), x2.clone()],
        );

        // Literal 1: not f(x0, x1, x2) = true (negative Bool equality)
        let lit1 = Literal::new(false, f_args.clone(), Term::new_true());

        // Literal 2: x2 = true (positive Bool equality)
        let lit2 = Literal::new(true, x2.clone(), Term::new_true());

        // Context: x0:Foo, x1:Foo, x2:Bool
        let context =
            LocalContext::from_types(vec![type_foo.clone(), type_foo.clone(), type_bool.clone()]);

        // Normalize the clause
        let (clause, _trace) = Clause::normalize_with_trace(vec![lit1, lit2], &context);

        // After normalization, check the output context:
        // Should have 3 variables with types Foo, Foo, Bool
        // The order may vary but the types should be consistent
        assert_eq!(clause.context.len(), 3);

        // Count how many Foo and Bool types we have
        let mut foo_count = 0;
        let mut bool_count = 0;
        for i in 0..clause.context.len() {
            match clause.context.get_var_type(i) {
                Some(t) if *t == type_foo => foo_count += 1,
                Some(t) if *t == type_bool => bool_count += 1,
                _ => panic!("Unexpected type in context"),
            }
        }
        assert_eq!(foo_count, 2, "Should have 2 Foo variables");
        assert_eq!(bool_count, 1, "Should have 1 Bool variable");

        // Specifically check that the literal that is just a variable (from lit2)
        // has the correct Bool type in the context
        for lit in &clause.literals {
            if lit.left.is_atomic() {
                if let Atom::FreeVariable(var_id) = lit.left.get_head_atom() {
                    let var_type = clause.context.get_var_type(*var_id as usize).unwrap();
                    assert_eq!(
                        *var_type, type_bool,
                        "Variable in atomic Bool literal should have Bool type, got {:?}",
                        var_type
                    );
                }
            }
        }
    }

    /// Test that validation catches applying a Bool to a Bool (c0(c1) where both are Bool).
    #[test]
    #[should_panic(expected = "Function type expected")]
    fn test_validation_catches_bool_applied_to_bool() {
        let mut kctx = KernelContext::new();
        kctx.add_constants(&["c0", "c1"], "Bool");
        // c0 and c1 are both Bool, so c0(c1) is invalid - can't apply Bool to Bool
        kctx.make_clause("c0(c1)", &[]);
    }

    /// Test that validation catches type mismatches in literals (left and right have different types).
    #[test]
    #[should_panic(expected = "Literal type mismatch")]
    fn test_validation_catches_literal_type_mismatch() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("g0", "Bool -> Bool")
            .add_constant("c0", "Bool");
        // g0 is Bool -> Bool, c0 is Bool, so g0 = c0 is a type mismatch
        kctx.make_clause("g0 = c0", &[]);
    }

    /// Test that validation catches missing variable types in context.
    #[test]
    #[should_panic(expected = "context has no type for it")]
    fn test_validation_catches_missing_variable_type() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("c0", "Bool");
        // x0 is used but no variable types provided
        kctx.make_clause("x0 = c0", &[]);
    }

    /// Test that valid clauses pass validation.
    #[test]
    fn test_valid_clause_passes_validation() {
        let mut kctx = KernelContext::new();
        kctx.add_constant("g0", "Bool -> Bool")
            .add_constants(&["c0", "c1"], "Bool");
        // g0(c0) is Bool -> Bool applied to Bool = Bool, c1 is Bool, so this is valid
        let clause = kctx.make_clause("g0(c0) = c1", &[]);
        assert_eq!(clause.literals.len(), 1);
    }

    /// Test that validation catches variables with Empty type.
    #[test]
    #[should_panic(expected = "has Empty type")]
    fn test_validation_catches_empty_type() {
        let kctx = KernelContext::new();
        // Create a context with a variable that has Empty type
        let context = LocalContext::from_types(vec![Term::empty_type()]);
        // Create a simple literal using x0
        let term = Term::atom(Atom::FreeVariable(0));
        let literal = Literal::positive(term);
        let clause = Clause::new(vec![literal], &context);
        // Validation should panic
        clause.validate(&kctx);
    }

    /// Test that extensionality works with asymmetric arities.
    /// This is the case from the no_mono_symbols bug:
    /// g0(c0, c1, x0) = g1(c0, x0) where c0, c1 are ground constants, x0 is free var
    /// The trailing x0 matches on both sides, so we should be able to peel x0:
    /// g0(c0, c1) = g1(c0)
    #[test]
    fn test_extensionality_asymmetric_arities() {
        let mut kctx = KernelContext::new();
        // c0 and c1 are ground type constants (like type parameters T and Nat)
        // g0 takes 3 args: T, Nat, value -> result
        // g1 takes 2 args: T, value -> result
        kctx.add_constant("c0", "Bool")
            .add_constant("c1", "Bool")
            .add_constant("g0", "Bool -> Bool -> Bool -> Bool")
            .add_constant("g1", "Bool -> Bool -> Bool");

        // Create clause: g0(c0, c1, x0) = g1(c0, x0)
        // This represents: intersection_family(T, Nat, seq) = seq_intersection(T, seq)
        let clause = kctx.make_clause("g0(c0, c1, x0) = g1(c0, x0)", &["Bool"]);

        // Extensionality should work: x0 is a free variable at the end of both sides
        let result = clause.find_extensionality(&kctx);
        assert!(
            result.is_some(),
            "Extensionality should work with asymmetric arities when trailing args match"
        );

        // Result should be g0(c0, c1) = g1(c0)
        let result_lits = result.unwrap();
        assert_eq!(result_lits.len(), 1);
        let result_lit = &result_lits[0];
        // g0 side should have 2 args (c0, c1)
        // g1 side should have 1 arg (c0)
        let (longer, shorter) = if result_lit.left.num_args() >= result_lit.right.num_args() {
            (&result_lit.left, &result_lit.right)
        } else {
            (&result_lit.right, &result_lit.left)
        };
        assert_eq!(longer.num_args(), 2, "g0 should have 2 args after peeling");
        assert_eq!(shorter.num_args(), 1, "g1 should have 1 arg after peeling");
    }
}
