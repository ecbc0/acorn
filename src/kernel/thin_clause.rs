use serde::{Deserialize, Serialize};

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::thin_literal::ThinLiteral;

/// A thin clause stores the structure of a clause without type information.
/// Like Clause, it represents a disjunction (an "or") of literals.
/// Type information is stored separately in the TypeStore and SymbolTable,
/// along with a Context that tracks the types of variables in the clause.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct ThinClause {
    pub literals: Vec<ThinLiteral>,
    pub context: LocalContext,
}

impl ThinClause {
    /// Get the local context for this clause.
    /// This returns the context that stores variable types for this clause.
    pub fn get_local_context(&self) -> &LocalContext {
        &self.context
    }

    /// Creates a new normalized clause.
    pub fn new(literals: Vec<ThinLiteral>, context: &LocalContext) -> ThinClause {
        let mut c = ThinClause {
            literals,
            context: context.clone(),
        };
        c.normalize();
        c
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
    pub fn normalize_var_ids(&mut self) {
        let mut var_ids = vec![];
        for literal in &mut self.literals {
            literal.normalize_var_ids(&mut var_ids);
        }
    }

    /// Create an impossible clause (empty clause, represents false).
    pub fn impossible() -> ThinClause {
        ThinClause {
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

    /// Count the number of positive literals.
    pub fn num_positive_literals(&self) -> usize {
        self.literals.iter().filter(|x| x.positive).count()
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
    pub fn contains(&self, other: &ThinClause) -> bool {
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
    pub fn normalize_var_ids_no_flip(&mut self) {
        let mut var_ids = vec![];
        for literal in &mut self.literals {
            literal.left.normalize_var_ids(&mut var_ids);
            literal.right.normalize_var_ids(&mut var_ids);
        }
    }

    /// Create a clause from literals without normalizing.
    pub fn from_literals_unnormalized(
        literals: Vec<ThinLiteral>,
        context: &LocalContext,
    ) -> ThinClause {
        ThinClause {
            literals,
            context: context.clone(),
        }
    }

    /// Create a clause from a single literal.
    pub fn from_literal(literal: ThinLiteral, context: &LocalContext) -> ThinClause {
        ThinClause::new(vec![literal], context)
    }

    /// Validate that all literals have consistent types.
    pub fn validate(&self, kernel_context: &KernelContext) {
        for literal in &self.literals {
            literal.validate_type(&self.context, kernel_context);
        }
    }

    /// Parse a clause from a string.
    /// Format: "lit1 | lit2 | lit3" where each literal is parsed by ThinLiteral::parse.
    pub fn parse(s: &str, context: &LocalContext) -> ThinClause {
        let literals: Vec<ThinLiteral> = s
            .split(" | ")
            .map(|part| ThinLiteral::parse(part.trim()))
            .collect();
        ThinClause::new(literals, context)
    }

    /// Renumbers synthetic atoms from the provided list into the invalid range.
    pub fn invalidate_synthetics(&self, from: &[AtomId]) -> ThinClause {
        let new_literals: Vec<ThinLiteral> = self
            .literals
            .iter()
            .map(|lit| lit.invalidate_synthetics(from))
            .collect();
        ThinClause::new(new_literals, &self.context)
    }

    /// Replace the first `num_to_replace` variables with invalid synthetic atoms.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> ThinClause {
        let new_literals: Vec<ThinLiteral> = self
            .literals
            .iter()
            .map(|lit| lit.instantiate_invalid_synthetics(num_to_replace))
            .collect();
        // The context needs to be adjusted - the first num_to_replace var types are removed
        let new_var_types: Vec<_> = self
            .context
            .var_types
            .iter()
            .skip(num_to_replace)
            .copied()
            .collect();
        let new_context = LocalContext::new(new_var_types);
        ThinClause::new(new_literals, &new_context)
    }

    /// Extracts the polarity from all literals.
    /// Returns a clause with all positive literals and a vector of the original polarities.
    pub fn extract_polarity(&self) -> (ThinClause, Vec<bool>) {
        let mut polarities = Vec::new();
        let mut new_literals = Vec::new();
        for literal in &self.literals {
            let (pos_lit, polarity) = literal.extract_polarity();
            new_literals.push(pos_lit);
            polarities.push(polarity);
        }
        (
            ThinClause::from_literals_unnormalized(new_literals, &self.context),
            polarities,
        )
    }
}
