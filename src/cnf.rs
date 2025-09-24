use std::vec;

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
    /// Creates a new CNF from a vector of clauses.
    fn new(clauses: Vec<Vec<Literal>>) -> Self {
        CNF(clauses)
    }

    /// Creates an empty CNF representing "true".
    pub fn true_value() -> Self {
        CNF(vec![])
    }

    pub fn is_true_value(&self) -> bool {
        self.0.is_empty()
    }

    /// Creates a CNF with an empty clause representing "false".
    pub fn false_value() -> Self {
        CNF(vec![vec![]])
    }

    pub fn is_false_value(&self) -> bool {
        self.0.len() == 1 && self.0[0].is_empty()
    }

    pub fn validate(&self) {
        for clause in &self.0 {
            for literal in clause {
                literal.validate();
            }
        }
    }

    /// Creates a CNF from a single literal.
    pub fn from_literal(literal: Literal) -> Self {
        if literal.is_true_value() {
            Self::true_value()
        } else if literal.is_false_value() {
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

    pub fn into_iter(self) -> impl Iterator<Item = Vec<Literal>> {
        self.0.into_iter()
    }

    pub fn to_literal(self) -> Option<Literal> {
        if self.is_true_value() {
            Some(Literal::true_value())
        } else if self.is_false_value() {
            Some(Literal::false_value())
        } else if self.0.len() == 1 && self.0[0].len() == 1 {
            Some(
                self.0
                    .into_iter()
                    .next()
                    .unwrap()
                    .into_iter()
                    .next()
                    .unwrap(),
            )
        } else {
            None
        }
    }

    /// Convert an if-then-else structure among literals into CNF.
    pub fn literal_if(condition: Literal, consequence: Literal, alternative: Literal) -> Self {
        CNF::new(vec![
            vec![condition.negate(), consequence],
            vec![condition, alternative],
        ])
    }

    /// Convert an if a { b } else { c } structure among CNF formulas into CNF.
    pub fn cnf_if(a: Literal, b: CNF, c: CNF) -> Self {
        let not_a_lit = CNF::from_literal(a.negate());
        let a_lit = CNF::from_literal(a);
        let not_a_imp_c = a_lit.or(c);
        let a_imp_b = not_a_lit.or(b);
        a_imp_b.and(not_a_imp_c)
    }
}
