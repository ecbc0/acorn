use crate::kernel::fat_clause::FatClause;
use crate::kernel::fat_literal::FatLiteral;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::variable_map::VariableMap;

/// A record of what happened to a literal during a transformation.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum LiteralTrace {
    /// This literal is in the output clause.
    Output { index: usize, flipped: bool },

    /// This literal was eliminated by combining with the given step.
    /// Step must be a single literal.
    Eliminated { step: usize, flipped: bool },

    /// This literal was self-contradictory, of the form x != x.
    Impossible,
}

impl LiteralTrace {
    pub fn flip(&mut self) {
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

/// A record of how a Clause was created from a particular Vec<Literal>.
/// The trace matches the original Vec<Literal> in length, not the clause necessarily.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ClauseTrace(Vec<LiteralTrace>);

impl ClauseTrace {
    pub fn new(traces: Vec<LiteralTrace>) -> ClauseTrace {
        ClauseTrace(traces)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn get(&self, index: usize) -> &LiteralTrace {
        &self.0[index]
    }

    pub fn get_mut(&mut self, index: usize) -> &mut LiteralTrace {
        &mut self.0[index]
    }

    pub fn into_inner(self) -> Vec<LiteralTrace> {
        self.0
    }

    pub fn as_slice(&self) -> &[LiteralTrace] {
        &self.0
    }

    pub fn iter(&self) -> std::slice::Iter<LiteralTrace> {
        self.0.iter()
    }

    pub fn compose(&mut self, other: &ClauseTrace) {
        for i in 0..self.0.len() {
            let LiteralTrace::Output { index, flipped } = self.0[i] else {
                continue;
            };
            self.0[i] = other.0[index].clone();
            if flipped {
                self.0[i].flip();
            }
        }
    }

    /// Validate that this trace, when applied to the given literals, produces the given clause.
    pub fn validate(
        &self,
        literals: &Vec<FatLiteral>,
        clause: &FatClause,
        kernel_context: &KernelContext,
    ) {
        let local_context = clause.get_local_context();
        let mut covered = vec![false; clause.len()];
        assert_eq!(self.len(), literals.len());
        let mut var_map = VariableMap::new();
        for (trace, literal) in self.iter().zip(literals) {
            match trace {
                LiteralTrace::Output { index, flipped } => {
                    let (left, right) = if *flipped {
                        (&literal.right, &literal.left)
                    } else {
                        (&literal.left, &literal.right)
                    };
                    covered[*index] = true;
                    let out = &clause.literals[*index];
                    assert!(var_map.match_terms(&left, &out.left, local_context, kernel_context));
                    assert!(var_map.match_terms(&right, &out.right, local_context, kernel_context));
                }
                _ => {
                    // The other branches don't leave anything to be validated
                }
            }
        }
    }
}
