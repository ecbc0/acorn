use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
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
    /// Convert an AcornValue to a QCF.
    /// Only handles cases that map directly onto QCF structure.
    /// Returns an error for unsupported cases.
    pub fn from_value(
        value: &AcornValue,
        normalizer: &mut crate::normalizer::Normalizer,
        ctype: crate::normalization_map::NewConstantType,
    ) -> Result<QCF, String> {
        use crate::acorn_value::{AcornValue, BinaryOp};

        match value {
            AcornValue::ForAll(types, body) => {
                let body_qcf = QCF::from_value(body, normalizer, ctype)?;
                Ok(QCF::ForAll(types.clone(), Box::new(body_qcf)))
            }
            AcornValue::Exists(types, body) => {
                let body_qcf = QCF::from_value(body, normalizer, ctype)?;
                Ok(QCF::Exists(types.clone(), Box::new(body_qcf)))
            }
            AcornValue::Binary(BinaryOp::And, left, right) => {
                let left_qcf = QCF::from_value(left, normalizer, ctype)?;
                let right_qcf = QCF::from_value(right, normalizer, ctype)?;
                Ok(QCF::And(Box::new(left_qcf), Box::new(right_qcf)))
            }
            AcornValue::Binary(BinaryOp::Or, left, right) => {
                let left_qcf = QCF::from_value(left, normalizer, ctype)?;
                let right_qcf = QCF::from_value(right, normalizer, ctype)?;
                Ok(QCF::Or(Box::new(left_qcf), Box::new(right_qcf)))
            }
            AcornValue::Bool(true) => {
                // True is represented as empty CNF
                Ok(QCF::CNF(vec![]))
            }
            AcornValue::Bool(false) => {
                // False is represented as CNF with empty clause
                Ok(QCF::False)
            }
            _ => {
                // For other values, try to convert to a single literal
                // and wrap it in CNF
                match normalizer.literal_from_value(value, ctype) {
                    Ok(literal) => {
                        if literal.is_tautology() {
                            // x = x is always true
                            Ok(QCF::CNF(vec![]))
                        } else if literal.is_impossible() {
                            // x != x is always false
                            Ok(QCF::False)
                        } else {
                            // Single literal becomes a single clause
                            Ok(QCF::CNF(vec![vec![literal]]))
                        }
                    }
                    Err(e) => Err(format!("Cannot convert {} to QCF: {}", value, e)),
                }
            }
        }
    }

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

/// Replace variables starting at `first_binding_index` with the provided replacement terms.
/// `stack_size` tracks how many bound variables are currently in scope so we can
/// shift the replacement terms when descending under additional quantifiers.
pub fn replace_variables_in_qcf(
    qcf: QCF,
    first_binding_index: AtomId,
    stack_size: AtomId,
    replacements: &[Term],
) -> QCF {
    match qcf {
        QCF::ForAll(types, body) => {
            let new_stack_size = stack_size + types.len() as AtomId;
            QCF::ForAll(
                types,
                Box::new(replace_variables_in_qcf(
                    *body,
                    first_binding_index,
                    new_stack_size,
                    replacements,
                )),
            )
        }
        QCF::Exists(types, body) => {
            let new_stack_size = stack_size + types.len() as AtomId;
            QCF::Exists(
                types,
                Box::new(replace_variables_in_qcf(
                    *body,
                    first_binding_index,
                    new_stack_size,
                    replacements,
                )),
            )
        }
        QCF::And(left, right) => QCF::And(
            Box::new(replace_variables_in_qcf(
                *left,
                first_binding_index,
                stack_size,
                replacements,
            )),
            Box::new(replace_variables_in_qcf(
                *right,
                first_binding_index,
                stack_size,
                replacements,
            )),
        ),
        QCF::Or(left, right) => QCF::Or(
            Box::new(replace_variables_in_qcf(
                *left,
                first_binding_index,
                stack_size,
                replacements,
            )),
            Box::new(replace_variables_in_qcf(
                *right,
                first_binding_index,
                stack_size,
                replacements,
            )),
        ),
        QCF::CNF(clauses) => {
            let new_clauses = clauses
                .into_iter()
                .map(|clause| {
                    clause
                        .into_iter()
                        .map(|lit| {
                            replace_variables_in_literal(
                                lit,
                                first_binding_index,
                                stack_size,
                                replacements,
                            )
                        })
                        .collect()
                })
                .collect();
            QCF::CNF(new_clauses)
        }
        QCF::False => QCF::False,
    }
}

/// Replace variables in a literal
fn replace_variables_in_literal(
    lit: Literal,
    first_binding_index: AtomId,
    stack_size: AtomId,
    replacements: &[Term],
) -> Literal {
    Literal::new(
        lit.positive,
        replace_variables_in_term(lit.left, first_binding_index, stack_size, replacements),
        replace_variables_in_term(lit.right, first_binding_index, stack_size, replacements),
    )
}

/// Replace variables in a term
fn replace_variables_in_term(
    term: Term,
    first_binding_index: AtomId,
    stack_size: AtomId,
    replacements: &[Term],
) -> Term {
    match term.head {
        Atom::Variable(i) => {
            if i < first_binding_index {
                let new_args = term
                    .args
                    .into_iter()
                    .map(|arg| {
                        replace_variables_in_term(
                            arg,
                            first_binding_index,
                            stack_size,
                            replacements,
                        )
                    })
                    .collect();
                Term::new(term.term_type, term.head_type, Atom::Variable(i), new_args)
            } else if i < first_binding_index + replacements.len() as AtomId {
                let index = (i - first_binding_index) as usize;
                let mut replacement = replacements[index].clone();
                let increment = stack_size - first_binding_index;
                replacement = shift_term(replacement, first_binding_index, increment);

                if term.args.is_empty() {
                    replacement
                } else {
                    let Term {
                        head_type: replacement_head_type,
                        head: replacement_head,
                        args: mut replacement_args,
                        ..
                    } = replacement;

                    for arg in term.args {
                        replacement_args.push(replace_variables_in_term(
                            arg,
                            first_binding_index,
                            stack_size,
                            replacements,
                        ));
                    }
                    Term::new(
                        term.term_type,
                        replacement_head_type,
                        replacement_head,
                        replacement_args,
                    )
                }
            } else {
                let new_index = i - replacements.len() as AtomId;
                let new_args = term
                    .args
                    .into_iter()
                    .map(|arg| {
                        replace_variables_in_term(
                            arg,
                            first_binding_index,
                            stack_size,
                            replacements,
                        )
                    })
                    .collect();
                Term::new(
                    term.term_type,
                    term.head_type,
                    Atom::Variable(new_index),
                    new_args,
                )
            }
        }
        _ => {
            let new_args = term
                .args
                .into_iter()
                .map(|arg| {
                    replace_variables_in_term(arg, first_binding_index, stack_size, replacements)
                })
                .collect();
            Term::new(term.term_type, term.head_type, term.head, new_args)
        }
    }
}
