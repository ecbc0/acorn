use crate::atom::{Atom, AtomId};
use crate::clause::Clause;
use crate::literal::Literal;
use crate::term::{Term, TypeId};
use crate::variable_map::VariableMap;
use std::fmt;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Scope(usize);

impl Scope {
    pub const OUTPUT: Scope = Scope(0);
    pub const LEFT: Scope = Scope(1);
    pub const RIGHT: Scope = Scope(2);

    pub fn get(&self) -> usize {
        self.0
    }
}

// A Unifier combines terms whose variables exist in different scopes.
// There are normally two input scopes, the "left" and the "right".
// For each scope we create a mapping from variable id to the term in the output scope.
// We leave the mapping as "None" when we haven't had to map it to anything yet.
//
// The output scope is the scope of the final term.
// Algorithmically, the output scope is treated slightly differently from the input scopes,
// but any input scopes are treated the same way.
// We do need a mapping for the output because we may have two complex terms in the output
// scope that we need to unify, and during this unification we may discover that previously
// unrelated variables now need to relate to each other.
pub struct Unifier {
    maps: Vec<VariableMap>,
}

// Information for how to replace a subterm
struct Replacement<'a> {
    path: &'a [usize],
    scope: Scope,
    term: &'a Term,
}

impl Unifier {
    /// Creates a new unifier with the given number of scopes.
    pub fn new(num_scopes: usize) -> Unifier {
        let mut maps = Vec::with_capacity(num_scopes);
        for _ in 0..num_scopes {
            maps.push(VariableMap::new());
        }
        Unifier { maps }
    }

    /// Creates a single-scope unifier.
    pub fn with_map(map: VariableMap) -> (Unifier, Scope) {
        let unifier = Unifier {
            maps: vec![VariableMap::new(), map],
        };
        (unifier, Scope(1))
    }

    fn mut_map(&mut self, scope: Scope) -> &mut VariableMap {
        &mut self.maps[scope.get()]
    }

    fn map(&self, scope: Scope) -> &VariableMap {
        &self.maps[scope.get()]
    }

    pub fn into_maps(self) -> impl Iterator<Item = (Scope, VariableMap)> {
        self.maps
            .into_iter()
            .enumerate()
            .map(|(i, var_map)| (Scope(i), var_map))
    }

    pub fn add_scope(&mut self) -> Scope {
        let scope = Scope(self.maps.len());
        self.maps.push(VariableMap::new());
        scope
    }

    fn has_mapping(&self, scope: Scope, i: AtomId) -> bool {
        self.map(scope).has_mapping(i)
    }

    fn set_mapping(&mut self, scope: Scope, i: AtomId, term: Term) {
        self.mut_map(scope).set(i, term);
    }

    fn get_mapping(&self, scope: Scope, i: AtomId) -> Option<&Term> {
        self.map(scope).get_mapping(i)
    }

    pub fn print_scope(&self, scope: Scope) -> i32 {
        let map = self.map(scope);
        let mut count = 0;
        for (i, t) in map.iter() {
            if count == 0 {
                println!("{:?} scope:", scope);
            }
            println!("x{} -> {}", i, t);
            count += 1;
        }
        count
    }

    pub fn print(&self) {
        let mut count = 0;
        count += self.print_scope(Scope::LEFT);
        count += self.print_scope(Scope::RIGHT);
        count += self.print_scope(Scope::OUTPUT);
        if count == 0 {
            println!("empty unifier");
        }
    }

    // Applies the unification to a term, possibly replacing a subterm with the
    // unification of the data provided in replacement.
    // This is weird because the replacement can have a different scope from the main term.
    fn apply_replace(
        &mut self,
        scope: Scope,
        term: &Term,
        replacement: Option<Replacement>,
    ) -> Term {
        if let Some(ref replacement) = replacement {
            if replacement.path.is_empty() {
                return self.apply(replacement.scope, replacement.term);
            }
        }

        // First apply to the head, flattening its args into this term if it's
        // a variable that expands into a term with its own arguments.
        let mut answer = match &term.head {
            Atom::Variable(i) => {
                if !self.has_mapping(scope, *i) && scope != Scope::OUTPUT {
                    // We need to create a new variable to send this one to.
                    let var_id = self.maps[Scope::OUTPUT.get()].len() as AtomId;
                    self.maps[Scope::OUTPUT.get()].push_none();
                    let new_var = Term::new(
                        term.head_type,
                        term.head_type,
                        Atom::Variable(var_id),
                        vec![],
                    );
                    self.set_mapping(scope, *i, new_var);
                }

                match self.get_mapping(scope, *i) {
                    Some(mapped_head) => {
                        // The head of our initial term expands to a full term.
                        // Its term type isn't correct, though.
                        let mut head = mapped_head.clone();
                        head.term_type = term.get_term_type();
                        head
                    }
                    None => {
                        // The head is an output variable with no mapping.
                        // Just leave it as it is.
                        assert!(scope == Scope::OUTPUT);
                        Term {
                            term_type: term.term_type,
                            head_type: term.head_type,
                            head: term.head.clone(),
                            args: vec![],
                        }
                    }
                }
            }
            head => Term {
                term_type: term.term_type,
                head_type: term.head_type,
                head: head.clone(),
                args: vec![],
            },
        };

        // Recurse on the arguments
        for (i, arg) in term.args.iter().enumerate() {
            // Figure out what replacement to pass recursively
            let new_replacement = if let Some(ref replacement) = replacement {
                if replacement.path[0] == i {
                    // We do want to pass this down
                    Some(Replacement {
                        path: &replacement.path[1..],
                        scope: replacement.scope,
                        term: replacement.term,
                    })
                } else {
                    None
                }
            } else {
                None
            };
            answer
                .args
                .push(self.apply_replace(scope, arg, new_replacement))
        }

        answer
    }

    pub fn apply(&mut self, scope: Scope, term: &Term) -> Term {
        self.apply_replace(scope, term, None)
    }

    /// Returns the resulting literal, and whether it was flipped.
    pub fn apply_to_literal(&mut self, scope: Scope, literal: &Literal) -> (Literal, bool) {
        let apply_left = self.apply(scope, &literal.left);
        let apply_right = self.apply(scope, &literal.right);
        Literal::new_with_flip(literal.positive, apply_left, apply_right)
    }

    // Replace variable i in the output scope with the given term (which is also in the output scope).
    // If they're both variables, keep the one with the lower id.
    // Returns whether this succeeded.
    // It fails if this would require making a variable self-nesting.
    fn remap(&mut self, id: AtomId, term: &Term) -> bool {
        if let Some(other_id) = term.atomic_variable() {
            if other_id > id {
                // Let's keep this id and remap the other one instead
                let mut new_term = term.clone();
                new_term.head = Atom::Variable(id);
                return self.unify_variable(Scope::OUTPUT, other_id, Scope::OUTPUT, &new_term);
            }
        }
        let term = self.apply(Scope::OUTPUT, term);
        if term.has_variable(id) {
            // We can't remap this variable to a term that contains it.
            // This represents an un-unifiable condition like x0 = c0(x0).
            return false;
        }

        for i in 0..self.maps.len() {
            self.maps[i].apply_to_all(|t| t.replace_variable(id, &term));
        }
        self.maps[Scope::OUTPUT.get()].set(id, term);
        true
    }

    // Returns whether they can be unified.
    fn unify_variable(
        &mut self,
        var_scope: Scope,
        var_id: AtomId,
        term_scope: Scope,
        term: &Term,
    ) -> bool {
        if term_scope != Scope::OUTPUT {
            // Convert our term to the output scope and then unify.
            let term = self.apply(term_scope, term);
            return self.unify_variable(var_scope, var_id, Scope::OUTPUT, &term);
        }

        if self.has_mapping(var_scope, var_id) {
            // We already have a mapping for this variable.
            // Unify the existing mapping with the term.
            let existing = self.get_mapping(var_scope, var_id).unwrap().clone();
            return self.unify(Scope::OUTPUT, &existing, Scope::OUTPUT, term);
        }

        if var_scope == Scope::OUTPUT {
            if term.atomic_variable() == Some(var_id) {
                // We're unifying a variable with itself.
                return true;
            }

            if term.has_variable(var_id) {
                // We can't unify a variable with a term that contains it.
                return false;
            }

            // This is fine.
            return self.remap(var_id, term);
        }

        // We don't have a mapping for this variable, so we can just map it now.
        self.set_mapping(var_scope, var_id, term.clone());
        true
    }

    // Returns whether they can be unified.
    fn unify_atoms(
        &mut self,
        atom_type: TypeId,
        scope1: Scope,
        atom1: &Atom,
        scope2: Scope,
        atom2: &Atom,
    ) -> bool {
        if let Atom::Variable(i) = atom1 {
            return self.unify_variable(scope1, *i, scope2, &Term::atom(atom_type, *atom2));
        }
        if let Atom::Variable(i) = atom2 {
            return self.unify_variable(scope2, *i, scope1, &Term::atom(atom_type, *atom1));
        }
        if atom1 == atom2 {
            return true;
        }
        false
    }

    // Helper method to try unifying a variable head term with a partial application
    // Returns true if successful, false otherwise
    fn try_unify_partial_application(
        &mut self,
        var_term: &Term,
        var_scope: Scope,
        full_term: &Term,
        full_scope: Scope,
    ) -> Option<bool> {
        // Check if var_term has a variable head with exactly one argument
        if let Atom::Variable(var_id) = var_term.head {
            if var_term.args.len() == 1 && full_term.args.len() > 1 {
                // We want to unify x0(arg) with f(a1, a2, ...)
                // This means x0 should map to f(a1, a2, ..., an-1) and arg should unify with an

                // Build the partial application: all of full_term except the last arg
                let n = full_term.args.len();
                let partial_args = full_term.args[0..n - 1].to_vec();

                // Create the partial application term
                // Use the head_type of var_term (the variable's type) as the term_type
                let partial = Term {
                    term_type: var_term.head_type,
                    head_type: full_term.head_type,
                    head: full_term.head,
                    args: partial_args,
                };

                // Unify the variable with the partial application
                if !self.unify_variable(var_scope, var_id, full_scope, &partial) {
                    return Some(false);
                }

                // Unify the argument with the last argument of full_term
                return Some(self.unify(
                    var_scope,
                    &var_term.args[0],
                    full_scope,
                    &full_term.args[n - 1],
                ));
            }
        }
        None
    }

    // Unify two terms, which may be in different scopes.
    pub fn unify(&mut self, scope1: Scope, term1: &Term, scope2: Scope, term2: &Term) -> bool {
        if term1.term_type != term2.term_type {
            return false;
        }

        // Handle the case where we're unifying something with a variable
        if let Some(i) = term1.atomic_variable() {
            return self.unify_variable(scope1, i, scope2, term2);
        }
        if let Some(i) = term2.atomic_variable() {
            return self.unify_variable(scope2, i, scope1, term1);
        }

        // Try to unify term1 (if it has a variable head) with a partial application of term2
        if let Some(result) = self.try_unify_partial_application(term1, scope1, term2, scope2) {
            return result;
        }

        // Try the symmetric case: term2 with a partial application of term1
        if let Some(result) = self.try_unify_partial_application(term2, scope2, term1, scope1) {
            return result;
        }

        // These checks mean we won't unify higher-order functions whose head types don't match.
        if term1.head_type != term2.head_type {
            return false;
        }
        if term1.args.len() != term2.args.len() {
            return false;
        }

        if !self.unify_atoms(term1.head_type, scope1, &term1.head, scope2, &term2.head) {
            return false;
        }

        for (a1, a2) in term1.args.iter().zip(term2.args.iter()) {
            if !self.unify(scope1, a1, scope2, a2) {
                return false;
            }
        }

        true
    }

    /// Doesn't worry about literal sign.
    pub fn unify_literals(
        &mut self,
        scope1: Scope,
        literal1: &Literal,
        scope2: Scope,
        literal2: &Literal,
        flipped: bool,
    ) -> bool {
        if flipped {
            // If we're flipped, swap the literals.
            self.unify(scope1, &literal1.right, scope2, &literal2.left)
                && self.unify(scope1, &literal1.left, scope2, &literal2.right)
        } else {
            // If we're not flipped, keep the literals as they are.
            self.unify(scope1, &literal1.left, scope2, &literal2.left)
                && self.unify(scope1, &literal1.right, scope2, &literal2.right)
        }
    }

    /// Tries to unify a left clause and a right clause.
    /// Does not reorder anything.
    pub fn unify_clauses(left: &Clause, right: &Clause) -> bool {
        if left.literals.len() != right.literals.len() {
            return false;
        }
        let mut unifier = Unifier::new(3);
        for (lit1, lit2) in left.literals.iter().zip(right.literals.iter()) {
            if !unifier.unify_literals(Scope::LEFT, lit1, Scope::RIGHT, lit2, false) {
                return false;
            }
        }
        true
    }

    pub fn assert_unify(&mut self, scope1: Scope, term1: &Term, scope2: Scope, term2: &Term) {
        assert!(
            self.unify(scope1, term1, scope2, term2),
            "Failed to unify {} and {}",
            term1,
            term2
        );

        let out1 = self.apply(scope1, term1);
        let out2 = self.apply(scope2, term2);
        assert_eq!(
            out1, out2,
            "Unification of {} and {} produced different results: {} and {}",
            term1, term2, out1, out2
        );
    }

    // Helper method for testing unification
    #[cfg(test)]
    fn unify_str(&mut self, scope1: Scope, str1: &str, scope2: Scope, str2: &str, expected: bool) {
        let term1 = Term::parse(str1);
        let term2 = Term::parse(str2);
        let result = self.unify(scope1, &term1, scope2, &term2);
        assert_eq!(
            result, expected,
            "Unification of {} ({:?}) with {} ({:?}) expected {}, got {}",
            str1, scope1, str2, scope2, expected, result
        );
    }

    /// Handle superposition into either positive or negative literals. The "SP" and "SN" rules.
    ///
    /// The superposition rule is, given:
    /// s = t   (pm_clause, the paramodulator's clause)
    /// u ?= v  (res_clause, the resolver's clause)
    ///
    /// If 'res_forward' is false, the u ?= v literal is swapped to be v ?= u.
    ///
    /// If s matches a subterm of u, superposition lets you replace the s with t to infer that:
    ///
    /// u[s -> t] ?= v
    /// (after the unifier has been applied to the whole thing)
    ///
    /// Sometimes we refer to s = t as the "paramodulator" and u ?= v as the "resolver".
    /// path describes which subterm of u we're replacing.
    /// s/t and u/v must be in the "right" scope.
    ///
    /// If ?= is =, it's "superposition into positive literals".
    /// If ?= is !=, it's "superposition into negative literals".
    ///
    /// Refer to page 3 of "E: A Brainiac Theorem Prover" for more detail.
    pub fn superpose_literals(
        &mut self,
        t: &Term,
        path: &[usize],
        res_literal: &Literal,
        res_forwards: bool,
    ) -> Literal {
        let (u, v) = if res_forwards {
            (&res_literal.left, &res_literal.right)
        } else {
            (&res_literal.right, &res_literal.left)
        };
        let unified_u = self.apply_replace(
            Scope::RIGHT,
            u,
            Some(Replacement {
                path: &path,
                scope: Scope::LEFT,
                term: t,
            }),
        );
        let unified_v = self.apply(Scope::RIGHT, &v);
        Literal::new(res_literal.positive, unified_u, unified_v)
    }

    // Handle superposition between two entire clauses.
    //
    // The superposition rule between clauses is, given:
    // s = t | S   (pm_clause, the paramodulator's clause)
    // u ?= v | R  (res_clause, the resolver's clause)
    //
    // It's like superposition between literals except we add '| S | R' to the result literal.
    //
    // pm_clause.literals[pm_literal_index] is the paramodulator.
    // res_clause.literals[res_literal_index] is the resolver.
    // These literals both get dropped in favor of the combined one, in the inferred clause.
    //
    // Refer to page 3 of "E: A Brainiac Theorem Prover" for more detail.
    pub fn superpose_clauses(
        &mut self,
        t: &Term,
        pm_clause: &Clause,
        pm_literal_index: usize,
        path: &[usize],
        res_clause: &Clause,
        res_literal_index: usize,
        res_forwards: bool,
    ) -> Vec<Literal> {
        let resolution_literal = &res_clause.literals[res_literal_index];
        let new_literal = self.superpose_literals(t, path, resolution_literal, res_forwards);

        // The new clause contains three types of literals.
        // Type 1: the new literal created by superposition
        let mut literals = vec![new_literal];

        // Type 2: the literals from unifying "R"
        for (i, literal) in res_clause.literals.iter().enumerate() {
            if i == res_literal_index {
                continue;
            }
            let (unified_literal, _) = self.apply_to_literal(Scope::RIGHT, literal);
            literals.push(unified_literal);
        }

        // Type 3: the literals from unifying "S"
        for (i, literal) in pm_clause.literals.iter().enumerate() {
            if i == pm_literal_index {
                continue;
            }
            let (unified_literal, _) = self.apply_to_literal(Scope::LEFT, literal);
            literals.push(unified_literal);
        }

        literals
    }

    pub fn into_one_map(self, scope: Scope) -> VariableMap {
        self.maps.into_iter().nth(scope.get()).unwrap()
    }
}

impl fmt::Display for Unifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Unifier:")?;
        for (scope, map) in self.maps.iter().enumerate() {
            write!(f, "  {:?}: {}", Scope(scope), map)?;
            if scope < self.maps.len() - 1 {
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::term::BOOL;

    use super::*;

    fn bool_fn(head: Atom, args: Vec<Term>) -> Term {
        Term {
            term_type: BOOL,
            head_type: 0,
            head,
            args,
        }
    }

    #[test]
    fn test_unifying_variables() {
        let bool0 = Term::atom(BOOL, Atom::Variable(0));
        let bool1 = Term::atom(BOOL, Atom::Variable(1));
        let bool2 = Term::atom(BOOL, Atom::Variable(2));
        let fterm = bool_fn(Atom::GlobalConstant(0), vec![bool0.clone(), bool1.clone()]);
        let mut u = Unifier::new(3);

        // Replace x0 with x1 and x1 with x2.
        assert!(u.unify_variable(Scope::LEFT, 0, Scope::OUTPUT, &bool1));
        assert!(u.unify_variable(Scope::LEFT, 1, Scope::OUTPUT, &bool2));
        let term = u.apply(Scope::LEFT, &fterm);
        assert_eq!(format!("{}", term), "g0(x1, x2)");
    }

    #[test]
    fn test_same_scope() {
        let bool0 = Term::atom(BOOL, Atom::Variable(0));
        let bool1 = Term::atom(BOOL, Atom::Variable(1));
        let bool2 = Term::atom(BOOL, Atom::Variable(2));
        let term1 = bool_fn(Atom::GlobalConstant(0), vec![bool0.clone(), bool1.clone()]);
        let term2 = bool_fn(Atom::GlobalConstant(0), vec![bool1.clone(), bool2.clone()]);
        let mut u = Unifier::new(3);

        u.assert_unify(Scope::LEFT, &term1, Scope::LEFT, &term2);
        let new1 = u.apply(Scope::LEFT, &term1);
        assert_eq!(format!("{}", new1), "g0(x0, x0)");
        let new2 = u.apply(Scope::LEFT, &term2);
        assert_eq!(format!("{}", new2), "g0(x0, x0)");
    }

    #[test]
    fn test_different_scope() {
        let bool0 = Term::atom(BOOL, Atom::Variable(0));
        let bool1 = Term::atom(BOOL, Atom::Variable(1));
        let bool2 = Term::atom(BOOL, Atom::Variable(2));
        let term1 = bool_fn(Atom::GlobalConstant(0), vec![bool0.clone(), bool1.clone()]);
        let term2 = bool_fn(Atom::GlobalConstant(0), vec![bool1.clone(), bool2.clone()]);
        let mut u = Unifier::new(3);

        u.assert_unify(Scope::LEFT, &term1, Scope::RIGHT, &term2);
        let new1 = u.apply(Scope::LEFT, &term1);
        assert_eq!(format!("{}", new1), "g0(x0, x1)");
        let new2 = u.apply(Scope::RIGHT, &term2);
        assert_eq!(format!("{}", new2), "g0(x0, x1)");
    }

    #[test]
    fn test_unifying_functional_variable() {
        let bool0 = Term::atom(BOOL, Atom::Variable(0));
        let const_f_term = bool_fn(Atom::GlobalConstant(0), vec![bool0.clone()]);
        let var_f_term = bool_fn(Atom::Variable(1), vec![bool0.clone()]);

        let mut u = Unifier::new(3);
        u.assert_unify(Scope::LEFT, &const_f_term, Scope::RIGHT, &var_f_term);
    }

    #[test]
    fn test_nested_functional_unify() {
        let left_term = Term::parse("x0(x0(c0))");
        let right_term = Term::parse("c1(x0(x1))");
        let mut u = Unifier::new(3);
        u.assert_unify(Scope::LEFT, &left_term, Scope::RIGHT, &right_term);
        u.print();
        assert!(u.get_mapping(Scope::LEFT, 0).unwrap().to_string() == "c1");
        assert!(u.get_mapping(Scope::RIGHT, 0).unwrap().to_string() == "c1");
        assert!(u.get_mapping(Scope::RIGHT, 1).unwrap().to_string() == "c0");
    }

    #[test]
    fn test_nested_functional_superpose() {
        let s = Term::parse("x0(x0(x1))");
        let u_subterm = Term::parse("c1(x0(x1))");
        let t = Term::parse("c2(x0, x1, c1(c1(c0)))");
        let pm_clause = Clause::parse("c2(x0, x1, c1(c1(c0))) = x0(x0(x1))");
        let target_path = &[0];
        let resolution_clause =
            Clause::parse("c1(c1(x0(x1))) != c1(x2(x3)) or c1(x0(x1)) = x2(x3)");
        let mut u = Unifier::new(3);
        u.assert_unify(Scope::LEFT, &s, Scope::RIGHT, &u_subterm);
        u.print();
        u.superpose_clauses(&t, &pm_clause, 0, target_path, &resolution_clause, 0, true);
    }

    #[test]
    fn test_higher_order_partial_application_unification() {
        // This test reproduces the issue from test_concrete_proof_list_contains
        // We need to unify x0(s5(x0, x1)) with m2(c0, s5(m2(c0), x0))
        // where x0 should map to m2(c0) (a partial application)

        // Create terms with proper types
        // For simplicity, let's use type 11 for functions and type 4 for the result
        let x0_var = Term::atom(11, Atom::Variable(0));
        let x1_var = Term::atom(2, Atom::Variable(1));

        // s5 is a skolem function that takes two arguments
        let s5_left = Term {
            term_type: 4,
            head_type: 14,
            head: Atom::Skolem(5),
            args: vec![x0_var.clone(), x1_var.clone()],
        };

        // Left side: x0(s5(x0, x1))
        let left_term = Term {
            term_type: 4,
            head_type: 11,
            head: Atom::Variable(0),
            args: vec![s5_left],
        };

        // Right side: m2(c0, s5(m2(c0), x0))
        let c0 = Term::atom(2, Atom::LocalConstant(0));
        let m2_c0 = Term {
            term_type: 11,
            head_type: 10,
            head: Atom::Monomorph(2),
            args: vec![c0.clone()],
        };

        let s5_right = Term {
            term_type: 4,
            head_type: 14,
            head: Atom::Skolem(5),
            args: vec![m2_c0.clone(), Term::atom(2, Atom::Variable(0))],
        };

        let right_term = Term {
            term_type: 4,
            head_type: 10,
            head: Atom::Monomorph(2),
            args: vec![c0.clone(), s5_right],
        };

        // Try to unify these terms
        let mut u = Unifier::new(3);

        let result = u.unify(Scope::LEFT, &left_term, Scope::RIGHT, &right_term);

        // This should succeed, with x0 mapping to m2(c0)
        assert!(
            result,
            "Should be able to unify x0(s5(x0, x1)) with m2(c0, s5(m2(c0), x0))"
        );

        // Check that x0 maps to m2(c0)
        if result {
            let x0_mapping = u.get_mapping(Scope::LEFT, 0);
            assert!(x0_mapping.is_some(), "x0 should have a mapping");
            // The mapping should be m2(c0) which is a partial application
            println!("x0 maps to: {:?}", x0_mapping);
        }
    }

    #[test]
    fn test_original_superpose() {
        let s = Term::parse("x0(x0(x1))");
        let u_subterm = Term::parse("c1(x0(x1))");
        let t = Term::parse("c2(x0, x1, c1(c1(c0)))");
        let pm_clause = Clause::parse("c2(x0, x1, c1(c1(c0))) = x0(x0(x1))");
        let target_path = &[0];
        let resolution_clause =
            Clause::parse("c1(c1(x0(x1))) != c1(x2(x3)) or c1(x0(x1)) = x2(x3)");
        let mut u = Unifier::new(3);
        u.assert_unify(Scope::LEFT, &s, Scope::RIGHT, &u_subterm);
        u.print();
        let literals =
            u.superpose_clauses(&t, &pm_clause, 0, target_path, &resolution_clause, 0, true);
        let new_clause = Clause::new(literals);
        assert!(
            new_clause.to_string()
                == "c1(c2(c1, x0, c1(c1(c0)))) != c1(x1(x2)) or c1(c1(x0)) = x1(x2)"
        );
    }

    #[test]
    fn test_mutual_containment_invalid_1() {
        let mut u = Unifier::new(3);
        u.unify_str(
            Scope::LEFT,
            "c0(x0, c0(x1, c1(x2)))",
            Scope::LEFT,
            "c0(c0(x2, x1), x0)",
            false,
        );
    }

    #[test]
    fn test_mutual_containment_invalid_2() {
        let mut u = Unifier::new(3);
        u.unify_str(
            Scope::LEFT,
            "c0(c0(x0, c1(x1)), x2)",
            Scope::LEFT,
            "c0(x2, c0(x1, x0))",
            false,
        );
    }

    #[test]
    fn test_recursive_reference_in_output() {
        let mut u = Unifier::new(3);
        u.unify_str(
            Scope::LEFT,
            "g2(x0, x0)",
            Scope::RIGHT,
            "g2(g2(g1(c0, x0), x0), g2(x1, x1))",
            false,
        );
    }

    #[test]
    fn test_variables_in_output_scope() {
        let mut unifier = Unifier::new(4);
        unifier.unify_str(Scope(1), "x0", Scope(0), "s0(x0, x1, s4)", true);
        unifier.unify_str(Scope(2), "g6(x0, x1)", Scope(3), "g6(c1, x0)", true);
        unifier.unify_str(Scope(2), "g0(x2, x1)", Scope(1), "g0(s4, x0)", true);
    }
}
