use crate::acorn_type::AcornType;
use crate::literal::Literal;

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
}
