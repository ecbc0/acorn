use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::literal::Literal;
use crate::normalizer::Normalizer;

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
    pub fn from_value(value: &AcornValue, normalizer: &mut Normalizer) -> Result<QCF, String> {
        match value {
            AcornValue::ForAll(types, body) => {
                let body_qcf = QCF::from_value(body, normalizer)?;
                Ok(QCF::ForAll(types.clone(), Box::new(body_qcf)))
            }
            AcornValue::Exists(types, body) => {
                let body_qcf = QCF::from_value(body, normalizer)?;
                Ok(QCF::Exists(types.clone(), Box::new(body_qcf)))
            }
            AcornValue::Binary(BinaryOp::And, left, right) => {
                let left_qcf = QCF::from_value(left, normalizer)?;
                let right_qcf = QCF::from_value(right, normalizer)?;
                Ok(QCF::And(Box::new(left_qcf), Box::new(right_qcf)))
            }
            AcornValue::Binary(BinaryOp::Or, left, right) => {
                let left_qcf = QCF::from_value(left, normalizer)?;
                let right_qcf = QCF::from_value(right, normalizer)?;
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
                match normalizer.literal_from_value(value) {
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
}
