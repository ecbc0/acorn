use serde::{Deserialize, Serialize};

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
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
                if let crate::kernel::atom::Atom::Variable(var_id) = atom {
                    if context.get_var_closed_type(*var_id as usize).is_none() {
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

    /// Check if this clause contains any applied variables.
    pub fn has_any_applied_variable(&self) -> bool {
        self.literals.iter().any(|x| x.has_any_applied_variable())
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
                if let crate::kernel::atom::Atom::Variable(var_id) = atom {
                    if context.get_var_closed_type(*var_id as usize).is_none() {
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
    pub fn validate(&self, kernel_context: &KernelContext) {
        for literal in &self.literals {
            literal.validate_type(&self.context, kernel_context);
        }
    }

    /// Parse a clause from a string.
    /// Format: "lit1 or lit2 or lit3" where each literal is parsed by Literal::parse.
    pub fn parse(s: &str, context: &LocalContext) -> Clause {
        let literals: Vec<Literal> = s
            .split(" or ")
            .map(|part| Literal::parse(part.trim()))
            .collect();
        Clause::new(literals, context)
    }

    /// Renumbers synthetic atoms from the provided list into the invalid range.
    pub fn invalidate_synthetics(&self, from: &[AtomId]) -> Clause {
        let new_literals: Vec<Literal> = self
            .literals
            .iter()
            .map(|lit| lit.invalidate_synthetics(from))
            .collect();
        Clause::new(new_literals, &self.context)
    }

    /// Replace the first `num_to_replace` variables with invalid synthetic atoms.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> Clause {
        let new_literals: Vec<Literal> = self
            .literals
            .iter()
            .map(|lit| lit.instantiate_invalid_synthetics(num_to_replace))
            .collect();
        // The context needs to be adjusted - the first num_to_replace var types are removed
        let new_closed_types: Vec<_> = self
            .context
            .get_var_closed_types()
            .iter()
            .skip(num_to_replace)
            .cloned()
            .collect();
        let new_context = LocalContext::from_closed_types(new_closed_types);
        Clause::new(new_literals, &new_context)
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

        // Check if this is f(a, b, c, x1, x2, ..., xn) = g(x1, x2, ..., xn)
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

        let longer_args = longer.args();
        let shorter_args = shorter.args();
        let n = shorter_args.len();

        // Check if the last n arguments are identical
        let diff = longer_args.len() - n;
        for i in 0..n {
            if longer_args[diff + i] != shorter_args[i] {
                return None;
            }
        }

        // Check that the matching arguments are all distinct variables
        for i in 0..n {
            match shorter_args[i].atomic_variable() {
                Some(var_id) => {
                    // Make sure this variable isn't used elsewhere
                    for j in 0..n {
                        if i != j && shorter_args[j].has_variable(var_id) {
                            return None;
                        }
                    }
                    // Make sure this variable isn't in the "extra" args of the longer term
                    for j in 0..diff {
                        if longer_args[j].has_variable(var_id) {
                            return None;
                        }
                    }
                    // Make sure this variable isn't in the heads
                    if longer.get_head_atom().is_variable() || shorter.get_head_atom().is_variable()
                    {
                        return None;
                    }
                }
                None => return None,
            }
        }

        // We can apply extensionality
        // Build the new literal without the trailing arguments
        let new_longer = if diff == 0 {
            longer.get_head_term()
        } else {
            let mut components = vec![crate::kernel::term::TermComponent::Atom(
                *longer.get_head_atom(),
            )];
            for arg in &longer_args[..diff] {
                if arg.is_atomic() {
                    components.push(crate::kernel::term::TermComponent::Atom(
                        *arg.get_head_atom(),
                    ));
                } else {
                    components.push(crate::kernel::term::TermComponent::Application {
                        span: arg.components().len() as u16 + 1,
                    });
                    components.extend(arg.components().iter().copied());
                }
            }
            crate::kernel::term::Term::from_components(components)
        };

        let new_shorter = shorter.get_head_term();

        // Check the types are compatible
        let longer_type = new_longer.get_closed_type_with_context(&self.context, kernel_context);
        let shorter_type = new_shorter.get_closed_type_with_context(&self.context, kernel_context);
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
        use crate::kernel::closed_type::ClosedType;

        let bool_closed = ClosedType::bool();

        let mut answer = vec![];

        for i in 0..self.literals.len() {
            let literal = &self.literals[i];
            if literal
                .left
                .get_closed_type_with_context(&self.context, kernel_context)
                != bool_closed
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
    use crate::kernel::closed_type::ClosedType;
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
        let x0 = Term::atom(Atom::Variable(0));
        let literal = Literal::equals(g0, x0);

        let some_type = ClosedType::ground(GroundTypeId::new(2));
        let context = LocalContext::from_closed_types(vec![some_type]);
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
        let x0 = Term::atom(Atom::Variable(0));
        let f_x0 = Term::new(Atom::Symbol(Symbol::GlobalConstant(0)), vec![x0.clone()]);
        let literal = Literal::equals(f_x0.clone(), f_x0);

        let some_type = ClosedType::ground(GroundTypeId::new(2));
        let context = LocalContext::from_closed_types(vec![some_type]);
        let clause = Clause::from_literals_unnormalized(vec![literal], &context);

        // Extensionality should not match this clause since both sides use the same function
        assert!(
            clause.find_extensionality(&kernel_context).is_none(),
            "Extensionality should not match when functions are the same"
        );
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

        let type_foo = ClosedType::ground(GroundTypeId::new(2)); // Some non-Bool type
        let type_bool = ClosedType::ground(GroundTypeId::new(1)); // Bool

        // x0 and x1 are Foo, x2 is Bool
        let x0 = Term::atom(Atom::Variable(0));
        let x1 = Term::atom(Atom::Variable(1));
        let x2 = Term::atom(Atom::Variable(2));

        // Create f(x0, x1, x2) - a function application
        let f_args = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x0.clone(), x1.clone(), x2.clone()],
        );

        // Literal 1: not f(x0, x1, x2) = true (negative Bool equality)
        let lit1 = Literal::new(false, f_args.clone(), Term::atom(Atom::True));

        // Literal 2: x2 = true (positive Bool equality)
        let lit2 = Literal::new(true, x2.clone(), Term::atom(Atom::True));

        // Context: x0:Foo, x1:Foo, x2:Bool
        let context = LocalContext::from_closed_types(vec![
            type_foo.clone(),
            type_foo.clone(),
            type_bool.clone(),
        ]);

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
            match clause.context.get_var_closed_type(i) {
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
                if let Atom::Variable(var_id) = lit.left.get_head_atom() {
                    let var_type = clause
                        .context
                        .get_var_closed_type(*var_id as usize)
                        .unwrap();
                    assert_eq!(
                        *var_type, type_bool,
                        "Variable in atomic Bool literal should have Bool type, got {:?}",
                        var_type
                    );
                }
            }
        }
    }
}
