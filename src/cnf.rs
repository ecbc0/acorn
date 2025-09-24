use crate::literal::Literal;

/// A CNF (Conjunctive Normal Form) formula represented as a vector of clauses,
/// where each clause is a vector of literals.
///
/// An empty CNF (no clauses) represents "true".
/// A CNF containing an empty clause represents "false".
///
/// Note that these clauses are different from the "Clause" object because they are not
/// individually normalized. Variable ids have the same meaning across all clauses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CNF(Vec<Vec<Literal>>);

impl CNF {
    /// Creates an empty CNF representing "true".
    pub fn true_value() -> Self {
        CNF(vec![])
    }

    /// Creates a CNF with an empty clause representing "false".
    pub fn false_value() -> Self {
        CNF(vec![vec![]])
    }

    /// Creates a CNF from a single literal.
    pub fn from_literal(literal: Literal) -> Self {
        if literal.is_basic_true() {
            Self::true_value()
        } else if literal.is_basic_false() {
            Self::false_value()
        } else {
            CNF(vec![vec![literal]])
        }
    }

    /// The 'and' of two CNF formulas.
    /// Simply concatenates the clauses from both formulas.
    pub fn and(mut self, other: CNF) -> Self {
        self.0.extend(other.0);
        self
    }

    /// The 'or' of two CNF formulas.
    /// Applies the distributive law: (A ∧ B) ∨ (C ∧ D) = (A ∨ C) ∧ (A ∨ D) ∧ (B ∨ C) ∧ (B ∨ D)
    pub fn or(self, other: CNF) -> Self {
        let mut result_clauses = vec![];
        for left_clause in &self.0 {
            for right_clause in &other.0 {
                let mut combined_clause = left_clause.clone();
                combined_clause.extend(right_clause.clone());
                result_clauses.push(combined_clause);
            }
        }
        CNF(result_clauses)
    }
}
