use serde::{Deserialize, Serialize};

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::context::Context;
use crate::kernel::thin_literal::ThinLiteral;

/// A thin clause stores the structure of a clause without type information.
/// Like Clause, it represents a disjunction (an "or") of literals.
/// Type information is stored separately in the TypeStore and SymbolTable,
/// along with a Context that tracks the types of variables in the clause.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct ThinClause {
    pub literals: Vec<ThinLiteral>,
    pub context: Context,
}

impl ThinClause {
    pub fn new(literals: Vec<ThinLiteral>, context: Context) -> ThinClause {
        ThinClause { literals, context }
    }

    /// Create an impossible clause (empty clause, represents false).
    pub fn impossible() -> ThinClause {
        ThinClause {
            literals: vec![],
            context: Context::empty(),
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
    pub fn has_local_constant(&self) -> bool {
        self.literals.iter().any(|x| x.has_local_constant())
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

    /// Whether we are willing to turn this clause into a line of code in a proof.
    ///
    /// WARNING: This differs from FatClause::is_printable which also checks has_synthetic().
    /// ThinClause cannot check for synthetic atoms without a SymbolTable parameter.
    /// TODO: Add has_synthetic() that takes &SymbolTable, or add SymbolTable parameter here.
    pub fn is_printable(&self) -> bool {
        if self.len() > 1 {
            return false;
        }
        todo!("ThinClause::is_printable needs has_synthetic check - requires SymbolTable parameter")
    }
}
