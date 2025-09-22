use crate::acorn_type::AcornType;
use crate::atom::{Atom, AtomId};
use crate::clause::Clause;
use crate::literal::Literal;
use crate::term::Term;

/// A quantified formula over clauses: a tree of and/or/forall/exists whose leaves are clauses
/// (disjunctions of literals), with negations only at literals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QCF {
    /// Universal quantification over variables with their types
    ForAll(Vec<AcornType>, Box<QCF>),

    /// Existential quantification over variables with their types
    Exists(Vec<AcornType>, Box<QCF>),

    /// Conjunction of two formulas
    And(Box<QCF>, Box<QCF>),

    /// Disjunction of two formulas
    Or(Box<QCF>, Box<QCF>),

    /// Conjunctive Normal Form - a conjunction of clauses (leaf node)
    /// An empty list represents "true".
    /// Each inner Vec<Literal> is a disjunction, like a Clause that is not normalized.
    CNF(Vec<Vec<Literal>>),

    /// False literal (leaf node)
    False,
}

impl QCF {
    /// Create a new universal quantification
    pub fn forall(types: Vec<AcornType>, body: QCF) -> Self {
        QCF::ForAll(types, Box::new(body))
    }

    /// Create a new existential quantification
    pub fn exists(types: Vec<AcornType>, body: QCF) -> Self {
        QCF::Exists(types, Box::new(body))
    }

    /// Create a conjunction of two formulas
    pub fn and(left: QCF, right: QCF) -> Self {
        QCF::And(Box::new(left), Box::new(right))
    }

    /// Create a disjunction of two formulas
    pub fn or(left: QCF, right: QCF) -> Self {
        QCF::Or(Box::new(left), Box::new(right))
    }

    /// Create a CNF leaf node
    pub fn cnf(clauses: Vec<Vec<Literal>>) -> Self {
        QCF::CNF(clauses)
    }

    /// Convert this QCF into a Vec<Clause>.
    /// Returns an error if the formula contains existential quantifiers.
    pub fn into_clauses(self) -> Result<Vec<Clause>, String> {
        let mut universal = vec![];
        let qcf = self.remove_forall(&mut universal);

        match qcf.into_literal_lists() {
            Ok(Some(lists)) => Ok(lists
                .into_iter()
                .map(|literals| Clause::new(literals))
                .collect()),
            Ok(None) => Ok(vec![Clause::impossible()]),
            Err(e) => Err(e),
        }
    }

    /// Remove all ForAll quantifiers, collecting the types in the universal list.
    /// Also shifts variables in branches properly when combining And/Or nodes.
    fn remove_forall(self, universal: &mut Vec<AcornType>) -> QCF {
        match self {
            QCF::And(left, right) => {
                let original_num_quants = universal.len() as AtomId;
                let new_left = left.remove_forall(universal);
                let added_quants = universal.len() as AtomId - original_num_quants;

                let shifted_right = shift_qcf(*right, original_num_quants, added_quants);
                let new_right = Box::new(shifted_right).remove_forall(universal);
                QCF::And(Box::new(new_left), Box::new(new_right))
            }
            QCF::Or(left, right) => {
                let original_num_quants = universal.len() as AtomId;
                let new_left = left.remove_forall(universal);
                let added_quants = universal.len() as AtomId - original_num_quants;

                let shifted_right = shift_qcf(*right, original_num_quants, added_quants);
                let new_right = Box::new(shifted_right).remove_forall(universal);
                QCF::Or(Box::new(new_left), Box::new(new_right))
            }
            QCF::ForAll(new_quants, body) => {
                universal.extend(new_quants);
                body.remove_forall(universal)
            }
            other => other,
        }
    }

    /// Convert to literal lists for CNF conversion.
    /// Returns Ok(None) for false, Ok(Some(vec![])) for true.
    fn into_literal_lists(self) -> Result<Option<Vec<Vec<Literal>>>, String> {
        match self {
            QCF::And(left, right) => {
                let left = match left.into_literal_lists()? {
                    Some(left) => left,
                    None => return Ok(None),
                };
                let right = match right.into_literal_lists()? {
                    Some(right) => right,
                    None => return Ok(None),
                };
                let mut result = left;
                result.extend(right);
                Ok(Some(result))
            }
            QCF::Or(left, right) => {
                let left = left.into_literal_lists()?;
                let right = right.into_literal_lists()?;
                match (left, right) {
                    (None, None) => Ok(None),
                    (Some(result), None) | (None, Some(result)) => Ok(Some(result)),
                    (Some(left), Some(right)) => {
                        let mut results = vec![];
                        for left_clause in &left {
                            for right_clause in &right {
                                let mut combined = left_clause.clone();
                                combined.extend(right_clause.clone());
                                results.push(combined);
                            }
                        }
                        Ok(Some(results))
                    }
                }
            }
            QCF::CNF(clauses) => Ok(Some(clauses)),
            QCF::False => Ok(None),
            QCF::ForAll(_, _) => Err("Unexpected ForAll in into_literal_lists".to_string()),
            QCF::Exists(_, _) => {
                Err("Cannot convert formula with existential quantifiers to clauses".to_string())
            }
        }
    }
}

/// Helper function to shift variable indices in a QCF.
/// Every variable at index or higher gets incremented by increment.
fn shift_qcf(qcf: QCF, index: AtomId, increment: AtomId) -> QCF {
    if increment == 0 {
        return qcf;
    }
    match qcf {
        QCF::ForAll(types, body) => {
            // Variables bound by this ForAll are at the current stack level,
            // so we need to shift the body with an adjusted index
            let new_index = index + types.len() as AtomId;
            QCF::ForAll(types, Box::new(shift_qcf(*body, new_index, increment)))
        }
        QCF::Exists(types, body) => {
            let new_index = index + types.len() as AtomId;
            QCF::Exists(types, Box::new(shift_qcf(*body, new_index, increment)))
        }
        QCF::And(left, right) => QCF::And(
            Box::new(shift_qcf(*left, index, increment)),
            Box::new(shift_qcf(*right, index, increment)),
        ),
        QCF::Or(left, right) => QCF::Or(
            Box::new(shift_qcf(*left, index, increment)),
            Box::new(shift_qcf(*right, index, increment)),
        ),
        QCF::CNF(clauses) => {
            // Shift variables in all literals
            let new_clauses = clauses
                .into_iter()
                .map(|clause| {
                    clause
                        .into_iter()
                        .map(|lit| shift_literal(lit, index, increment))
                        .collect()
                })
                .collect();
            QCF::CNF(new_clauses)
        }
        QCF::False => QCF::False,
    }
}

/// Helper function to shift variable indices in a Literal.
fn shift_literal(lit: Literal, index: AtomId, increment: AtomId) -> Literal {
    Literal::new(
        lit.positive,
        shift_term(lit.left, index, increment),
        shift_term(lit.right, index, increment),
    )
}

/// Helper function to shift variable indices in a Term.
fn shift_term(term: Term, index: AtomId, increment: AtomId) -> Term {
    let new_head = match term.head {
        Atom::Variable(i) if i >= index => Atom::Variable(i + increment),
        other => other,
    };
    let new_args = term
        .args
        .into_iter()
        .map(|arg| shift_term(arg, index, increment))
        .collect();
    Term::new(term.term_type, term.head_type, new_head, new_args)
}

/// Replace variables starting at base_index with the given replacement terms.
pub fn replace_variables_in_qcf(qcf: QCF, base_index: AtomId, replacements: &[Term]) -> QCF {
    match qcf {
        QCF::ForAll(types, body) => {
            // Variables bound by this ForAll start after the replacements
            let new_base = base_index + replacements.len() as AtomId;
            QCF::ForAll(types, Box::new(replace_variables_in_qcf(*body, new_base, replacements)))
        }
        QCF::Exists(types, body) => {
            let new_base = base_index + replacements.len() as AtomId;
            QCF::Exists(types, Box::new(replace_variables_in_qcf(*body, new_base, replacements)))
        }
        QCF::And(left, right) => QCF::And(
            Box::new(replace_variables_in_qcf(*left, base_index, replacements)),
            Box::new(replace_variables_in_qcf(*right, base_index, replacements)),
        ),
        QCF::Or(left, right) => QCF::Or(
            Box::new(replace_variables_in_qcf(*left, base_index, replacements)),
            Box::new(replace_variables_in_qcf(*right, base_index, replacements)),
        ),
        QCF::CNF(clauses) => {
            let new_clauses = clauses.into_iter()
                .map(|clause| {
                    clause.into_iter()
                        .map(|lit| replace_variables_in_literal(lit, base_index, replacements))
                        .collect()
                })
                .collect();
            QCF::CNF(new_clauses)
        }
        QCF::False => QCF::False,
    }
}

/// Replace variables in a literal
fn replace_variables_in_literal(lit: Literal, base_index: AtomId, replacements: &[Term]) -> Literal {
    Literal::new(
        lit.positive,
        replace_variables_in_term(lit.left, base_index, replacements),
        replace_variables_in_term(lit.right, base_index, replacements),
    )
}

/// Replace variables in a term
fn replace_variables_in_term(term: Term, base_index: AtomId, replacements: &[Term]) -> Term {
    match term.head {
        Atom::Variable(i) if i >= base_index && (i - base_index) < replacements.len() as AtomId => {
            // Replace this variable with the corresponding replacement term
            let replacement = &replacements[(i - base_index) as usize];
            if term.args.is_empty() {
                replacement.clone()
            } else {
                // Apply the replacement term to the arguments
                let mut new_args = replacement.args.clone();
                for arg in term.args {
                    new_args.push(replace_variables_in_term(arg, base_index, replacements));
                }
                Term::new(term.term_type, replacement.head_type, replacement.head.clone(), new_args)
            }
        }
        _ => {
            let new_args = term
                .args
                .into_iter()
                .map(|arg| replace_variables_in_term(arg, base_index, replacements))
                .collect();
            Term::new(term.term_type, term.head_type, term.head, new_args)
        }
    }
}
