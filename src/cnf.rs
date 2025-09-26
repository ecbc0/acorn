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
        for lits in &self.0 {
            for lit in lits {
                if !lit.is_normalized() {
                    panic!("CNF contains non-normalized literal: {}", lit);
                }
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

    pub fn and_all(formulas: impl Iterator<Item = CNF>) -> Self {
        let mut result = CNF::true_value();
        for formula in formulas {
            result = result.and(formula);
        }
        result
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

    pub fn or_all(formulas: impl Iterator<Item = CNF>) -> Self {
        let mut result = CNF::false_value();
        for formula in formulas {
            result = result.or(formula);
        }
        result
    }

    // Note that this causes exponential blowup.
    // Think of the input formula as And(Or(...)).
    // To negate it, it's Negate(And(Or(...))), which is equivalent to Or(And(Negate(...))).
    pub fn negate(&self) -> CNF {
        CNF::or_all(
            self.0.iter().map(|clause| {
                CNF::and_all(clause.iter().map(|lit| CNF::from_literal(lit.negate())))
            }),
        )
    }

    pub fn into_iter(self) -> impl Iterator<Item = Vec<Literal>> {
        self.0.into_iter()
    }

    // Plain "true" or "false" are zero literals, not a single literal.
    fn is_single_literal(&self) -> bool {
        self.0.len() == 1 && self.0[0].len() == 1
    }

    fn as_single_literal(&self) -> Option<&Literal> {
        if self.is_single_literal() {
            Some(&self.0[0][0])
        } else {
            None
        }
    }

    fn into_single_literal(self) -> Literal {
        assert!(self.is_single_literal());
        self.0
            .into_iter()
            .next()
            .unwrap()
            .into_iter()
            .next()
            .unwrap()
    }

    pub fn is_literal(&self) -> bool {
        self.is_true_value() || self.is_false_value() || self.is_single_literal()
    }

    pub fn to_literal(self) -> Option<Literal> {
        if self.is_true_value() {
            Some(Literal::true_value())
        } else if self.is_false_value() {
            Some(Literal::false_value())
        } else if self.is_single_literal() {
            Some(self.into_single_literal())
        } else {
            None
        }
    }

    pub fn to_bool(&self) -> Option<bool> {
        if self.is_true_value() {
            Some(true)
        } else if self.is_false_value() {
            Some(false)
        } else {
            None
        }
    }

    fn maybe_transform_eq_to_literal(self, other: CNF) -> Result<Literal, (CNF, CNF)> {
        if let Some(self_bool) = self.to_bool() {
            if other.is_literal() {
                let other_lit = other.to_literal().unwrap();
                if self_bool {
                    Ok(other_lit)
                } else {
                    Ok(other_lit.negate())
                }
            } else {
                Err((self, other))
            }
        } else if let Some(other_bool) = other.to_bool() {
            if self.is_literal() {
                let self_lit = self.to_literal().unwrap();
                if other_bool {
                    Ok(self_lit)
                } else {
                    Ok(self_lit.negate())
                }
            } else {
                Err((self, other))
            }
        } else if self.is_single_literal() && other.is_single_literal() {
            let self_lit = self.as_single_literal().unwrap();
            let other_lit = other.as_single_literal().unwrap();
            if self_lit.right.is_true() && other_lit.right.is_true() {
                let self_lit = self.into_single_literal();
                let other_lit = other.into_single_literal();
                let positive = self_lit.positive == other_lit.positive;
                Ok(Literal::new(positive, self_lit.left, other_lit.left))
            } else {
                Err((self, other))
            }
        } else {
            Err((self, other))
        }
    }

    pub fn equals(self, other: CNF) -> CNF {
        match self.maybe_transform_eq_to_literal(other) {
            Ok(lit) => CNF::from_literal(lit),
            Err((a, b)) => {
                let neg_a = a.negate();
                let neg_b = b.negate();
                let a_imp_b = neg_a.or(b);
                let b_imp_a = neg_b.or(a);
                a_imp_b.and(b_imp_a)
            }
        }
    }

    pub fn not_equals(self, other: CNF) -> CNF {
        match self.maybe_transform_eq_to_literal(other) {
            Ok(lit) => CNF::from_literal(lit.negate()),
            Err((a, b)) => {
                let neg_a = a.negate();
                let neg_b = b.negate();
                let a_imp_not_b = neg_a.or(neg_b);
                let not_a_imp_b = a.or(b);
                a_imp_not_b.and(not_a_imp_b)
            }
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

    /// Parse a CNF formula from a string.
    /// The string should be in the format "clause1 and clause2 and ..."
    /// where each clause is "literal1 or literal2 or ...".
    pub fn parse(s: &str) -> Self {
        let clauses: Vec<Vec<Literal>> = s
            .split(" and ")
            .map(|clause_str| {
                clause_str
                    .split(" or ")
                    .map(|lit_str| Literal::parse(lit_str))
                    .collect()
            })
            .collect();
        CNF::new(clauses)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cnf_negate() {
        let cnf = CNF::parse("x0 or x1 and x2 or x3");

        let negated = cnf.negate();

        let expected = CNF::parse(
            "\
        not x0 or not x2 and \
        not x0 or not x3 and \
        not x1 or not x2 and \
        not x1 or not x3",
        );

        assert_eq!(negated, expected);
    }

    #[test]
    fn test_cnf_simple_equality() {
        let cnf1 = CNF::parse("x0");
        let cnf2 = CNF::parse("not x1");

        assert_eq!(cnf1.clone().equals(cnf2.clone()), CNF::parse("x0 != x1"));
        assert_eq!(cnf2.clone().equals(cnf1.clone()), CNF::parse("x0 != x1"));
        assert_eq!(cnf1.clone().not_equals(cnf2.clone()), CNF::parse("x0 = x1"));
        assert_eq!(cnf2.clone().not_equals(cnf1.clone()), CNF::parse("x0 = x1"));
    }
}
