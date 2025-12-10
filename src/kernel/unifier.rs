use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
#[cfg(test)]
use crate::kernel::closed_type::ClosedType;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
#[cfg(test)]
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Term;
use crate::kernel::term::TermRef;
use crate::kernel::variable_map::VariableMap;
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
pub struct Unifier<'a> {
    maps: Vec<VariableMap>,

    // Shared kernel context for symbol table access
    kernel_context: &'a KernelContext,

    // One LocalContext per input scope (borrowed from source clauses)
    // Index 0 is unused (that's the output scope), indices 1+ correspond to input scopes
    input_contexts: Vec<Option<&'a LocalContext>>,

    // Owned output context, built during unification as new variables are created
    output_context: LocalContext,
}

// Information for how to replace a subterm
struct Replacement<'a> {
    path: &'a [usize],
    scope: Scope,
    term: &'a Term,
}

impl<'a> Unifier<'a> {
    /// Creates a new unifier with the given number of scopes.
    pub fn new(num_scopes: usize, kernel_context: &'a KernelContext) -> Unifier<'a> {
        let mut maps = Vec::with_capacity(num_scopes);
        for _ in 0..num_scopes {
            maps.push(VariableMap::new());
        }
        // Initialize input_contexts with None for each scope (including output at index 0)
        let mut input_contexts = Vec::with_capacity(num_scopes);
        for _ in 0..num_scopes {
            input_contexts.push(None);
        }
        Unifier {
            maps,
            kernel_context,
            input_contexts,
            output_context: LocalContext::empty(),
        }
    }

    /// Sets the input context for a specific scope.
    /// Should be called for LEFT and RIGHT scopes before unification.
    pub fn set_input_context(&mut self, scope: Scope, context: &'a LocalContext) {
        self.input_contexts[scope.get()] = Some(context);
    }

    /// Returns a reference to the output context.
    pub fn output_context(&self) -> &LocalContext {
        &self.output_context
    }

    /// Consumes the unifier and returns the output context.
    pub fn take_output_context(self) -> LocalContext {
        self.output_context
    }

    /// Returns the kernel context.
    pub fn kernel_context(&self) -> &KernelContext {
        self.kernel_context
    }

    /// Pre-populates the output context with variable types for testing.
    /// This allows tests to directly use output variables without going through unification.
    #[cfg(test)]
    fn set_output_var_closed_types(&mut self, types: Vec<ClosedType>) {
        self.output_context = LocalContext::from_closed_types(types);
    }

    /// Returns the LocalContext for a given scope.
    /// For OUTPUT scope, returns the output_context.
    /// For input scopes (LEFT, RIGHT, etc.), returns the stored input context.
    fn get_local_context(&self, scope: Scope) -> &LocalContext {
        if scope == Scope::OUTPUT {
            &self.output_context
        } else {
            self.input_contexts[scope.get()].expect("Input context not set for scope")
        }
    }

    /// Creates a unifier with an initial VariableMap and explicit output context.
    /// The output_context provides the types for variables in the output scope.
    pub fn with_map(
        map: VariableMap,
        kernel_context: &'a KernelContext,
        output_context: LocalContext,
    ) -> (Unifier<'a>, Scope) {
        // Initialize the output map with enough blank entries for any variables in the initial map
        let mut output_map = VariableMap::new();
        if let Some(max_var) = map.max_output_variable() {
            for _ in 0..=max_var {
                output_map.push_none();
            }
        }

        let unifier = Unifier {
            maps: vec![output_map, map],
            kernel_context,
            input_contexts: vec![None, None], // Output scope and one input scope
            output_context,
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

    /// Like into_maps, but also returns the output context.
    /// This is needed because VariableMap replacement terms reference
    /// variables in the unifier's output context.
    pub fn into_maps_with_context(self) -> (Vec<(Scope, VariableMap)>, LocalContext) {
        let maps: Vec<_> = self
            .maps
            .into_iter()
            .enumerate()
            .map(|(i, var_map)| (Scope(i), var_map))
            .collect();
        (maps, self.output_context)
    }

    pub fn add_scope(&mut self) -> Scope {
        let scope = Scope(self.maps.len());
        self.maps.push(VariableMap::new());
        self.input_contexts.push(None);
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
        term: TermRef,
        replacement: Option<Replacement>,
    ) -> Term {
        if let Some(ref replacement) = replacement {
            if replacement.path.is_empty() {
                return self.apply(replacement.scope, replacement.term);
            }
        }

        // First figure out what the head expands to, if it's a variable.
        // We track the head atom and any args from the expansion separately.
        let (head, mut args) = match term.get_head_atom() {
            Atom::Variable(i) => {
                if !self.has_mapping(scope, *i) && scope != Scope::OUTPUT {
                    // We need to create a new variable to send this one to.
                    let var_id = self.maps[Scope::OUTPUT.get()].len() as AtomId;
                    self.maps[Scope::OUTPUT.get()].push_none();
                    // Track the type in output_context - get the variable's type directly from LocalContext
                    let var_closed_type = self
                        .get_local_context(scope)
                        .get_var_closed_type(*i as usize)
                        .cloned()
                        .expect("Variable should have type in LocalContext");
                    self.output_context.push_closed_type(var_closed_type);
                    let new_var = Term::new(Atom::Variable(var_id), vec![]);
                    self.set_mapping(scope, *i, new_var);
                }

                match self.get_mapping(scope, *i) {
                    Some(mapped_head) => {
                        // The head of our initial term expands to a full term.
                        // mapped_head is in OUTPUT scope since mappings produce output terms.
                        (mapped_head.get_head_atom().clone(), mapped_head.args())
                    }
                    None => {
                        // The head is an output variable with no mapping.
                        // Just leave it as it is.
                        assert!(scope == Scope::OUTPUT);
                        (term.get_head_atom().clone(), vec![])
                    }
                }
            }
            _head => (term.get_head_atom().clone(), vec![]),
        };

        // Recurse on the arguments and append them.
        for (i, arg) in term.iter_args().enumerate() {
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
            args.push(self.apply_replace(scope, arg, new_replacement))
        }

        Term::new(head, args)
    }

    pub fn apply(&mut self, scope: Scope, term: &Term) -> Term {
        self.apply_replace(scope, term.as_ref(), None)
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
                // Let's keep this id and remap the other one instead.
                // Since term is an atomic variable, create a new variable term with the lower id.
                let new_term = Term::new_variable(id);
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
            return self.unify_internal(
                Scope::OUTPUT,
                existing.as_ref(),
                Scope::OUTPUT,
                term.as_ref(),
            );
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
    fn unify_atoms(&mut self, scope1: Scope, atom1: &Atom, scope2: Scope, atom2: &Atom) -> bool {
        if let Atom::Variable(i) = atom1 {
            return self.unify_variable(scope1, *i, scope2, &Term::atom(*atom2));
        }
        if let Atom::Variable(i) = atom2 {
            return self.unify_variable(scope2, *i, scope1, &Term::atom(*atom1));
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
        var_term: TermRef,
        var_scope: Scope,
        full_term: TermRef,
        full_scope: Scope,
    ) -> Option<bool> {
        // Check if var_term has a variable head with arguments
        if let Atom::Variable(var_id) = *var_term.get_head_atom() {
            let var_args_len = var_term.num_args();
            let full_args_len = full_term.num_args();

            if var_args_len >= 1 && full_args_len > var_args_len {
                // We want to unify x0(arg1, ..., argN) with f(a1, ..., aM) where M > N
                // This means x0 should map to f(a1, ..., a(M-N))
                // and each argi should unify with a(M-N+i)

                // Build the partial application: first (M-N) args of full_term
                let num_partial_args = full_args_len - var_args_len;
                let full_args: Vec<_> = full_term.iter_args().collect();
                let partial_args: Vec<Term> = full_args[0..num_partial_args]
                    .iter()
                    .map(|arg| arg.to_owned())
                    .collect();

                // Create the partial application term
                let partial = Term::new(*full_term.get_head_atom(), partial_args);

                // Unify the variable with the partial application
                if !self.unify_variable(var_scope, var_id, full_scope, &partial) {
                    return Some(false);
                }

                // Unify each var_term argument with the corresponding full_term argument
                let var_args: Vec<_> = var_term.iter_args().collect();
                for i in 0..var_args_len {
                    if !self.unify_internal(
                        var_scope,
                        var_args[i],
                        full_scope,
                        full_args[num_partial_args + i],
                    ) {
                        return Some(false);
                    }
                }

                return Some(true);
            }
        }
        None
    }

    // Public interface for unification
    // Does not allow unification with the output scope - callers should not directly
    // provide terms in the output scope as the unifier manages output variables internally
    pub fn unify(&mut self, scope1: Scope, term1: &Term, scope2: Scope, term2: &Term) -> bool {
        if scope1 == Scope::OUTPUT || scope2 == Scope::OUTPUT {
            panic!("Cannot call unify with output scope - the unifier manages output variables internally");
        }
        self.unify_internal(scope1, term1.as_ref(), scope2, term2.as_ref())
    }

    // Internal unification implementation
    fn unify_internal(
        &mut self,
        scope1: Scope,
        term1: TermRef,
        scope2: Scope,
        term2: TermRef,
    ) -> bool {
        let local1 = self.get_local_context(scope1);
        let local2 = self.get_local_context(scope2);
        let kc = self.kernel_context;

        if term1.get_closed_type_with_context(local1, kc)
            != term2.get_closed_type_with_context(local2, kc)
        {
            return false;
        }

        // Handle the case where we're unifying something with a variable
        if let Some(i) = term1.atomic_variable() {
            return self.unify_variable(scope1, i, scope2, &term2.to_owned());
        }
        if let Some(i) = term2.atomic_variable() {
            return self.unify_variable(scope2, i, scope1, &term1.to_owned());
        }

        // Try to unify term1 (if it has a variable head) with a partial application of term2
        if let Some(result) = self.try_unify_partial_application(term1, scope1, term2, scope2) {
            return result;
        }

        // Try the symmetric case: term2 with a partial application of term1
        if let Some(result) = self.try_unify_partial_application(term2, scope2, term1, scope1) {
            return result;
        }

        // Re-get local contexts since we may have modified them above
        let local1 = self.get_local_context(scope1);
        let local2 = self.get_local_context(scope2);

        // These checks mean we won't unify higher-order functions whose types don't match.
        if term1.get_closed_type_with_context(local1, kc)
            != term2.get_closed_type_with_context(local2, kc)
        {
            return false;
        }
        if term1.num_args() != term2.num_args() {
            return false;
        }

        if !self.unify_atoms(scope1, term1.get_head_atom(), scope2, term2.get_head_atom()) {
            return false;
        }

        for (a1, a2) in term1.iter_args().zip(term2.iter_args()) {
            if !self.unify_internal(scope1, a1, scope2, a2) {
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
            self.unify_internal(
                scope1,
                literal1.right.as_ref(),
                scope2,
                literal2.left.as_ref(),
            ) && self.unify_internal(
                scope1,
                literal1.left.as_ref(),
                scope2,
                literal2.right.as_ref(),
            )
        } else {
            // If we're not flipped, keep the literals as they are.
            self.unify_internal(
                scope1,
                literal1.left.as_ref(),
                scope2,
                literal2.left.as_ref(),
            ) && self.unify_internal(
                scope1,
                literal1.right.as_ref(),
                scope2,
                literal2.right.as_ref(),
            )
        }
    }

    /// Tries to unify a left clause and a right clause.
    /// Does not reorder anything.
    pub fn unify_clauses(left: &Clause, right: &Clause, kernel_context: &KernelContext) -> bool {
        if left.literals.len() != right.literals.len() {
            return false;
        }
        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, left.get_local_context());
        unifier.set_input_context(Scope::RIGHT, right.get_local_context());
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
            u.as_ref(),
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

    /// Like into_one_map, but also returns the output context.
    /// This is needed because VariableMap replacement terms reference
    /// variables in the unifier's output context.
    pub fn into_one_map_with_context(self, scope: Scope) -> (VariableMap, LocalContext) {
        let map = self.maps.into_iter().nth(scope.get()).unwrap();
        (map, self.output_context)
    }
}

impl fmt::Display for Unifier<'_> {
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
    use super::*;

    fn bool_fn(head: Atom, args: Vec<Term>) -> Term {
        Term::new(head, args)
    }

    /// Creates a test KernelContext with proper function types for testing.
    /// g0: (Bool, Bool) -> Bool
    /// g1: Bool -> Bool
    /// g2: (Bool, Bool, Bool) -> Bool
    fn test_ctx() -> KernelContext {
        KernelContext::test_with_function_types()
    }

    /// Creates a test unifier with BOOL types for variables.
    /// Use this for tests that explicitly construct terms with BOOL types.
    fn test_unifier_bool<'a>(kernel_context: &'a KernelContext) -> Unifier<'a> {
        use crate::kernel::closed_type::ClosedType;
        use crate::kernel::local_context::LocalContext;
        let mut u = Unifier::new(3, kernel_context);
        u.set_input_context(Scope::LEFT, LocalContext::test_bool_ref());
        u.set_input_context(Scope::RIGHT, LocalContext::test_bool_ref());
        u.set_output_var_closed_types(vec![ClosedType::bool(); 10]);
        u
    }

    #[test]
    fn test_unifying_variables() {
        let ctx = test_ctx();
        let bool0 = Term::atom(Atom::Variable(0));
        let bool1 = Term::atom(Atom::Variable(1));
        let bool2 = Term::atom(Atom::Variable(2));
        let fterm = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![bool0.clone(), bool1.clone()],
        );
        let mut u = test_unifier_bool(&ctx);

        // Replace x0 with x1 and x1 with x2.
        assert!(u.unify_variable(Scope::LEFT, 0, Scope::OUTPUT, &bool1));
        assert!(u.unify_variable(Scope::LEFT, 1, Scope::OUTPUT, &bool2));
        let term = u.apply(Scope::LEFT, &fterm);
        assert_eq!(format!("{}", term), "g0(x1, x2)");
    }

    #[test]
    fn test_same_scope() {
        let ctx = test_ctx();
        let bool0 = Term::atom(Atom::Variable(0));
        let bool1 = Term::atom(Atom::Variable(1));
        let bool2 = Term::atom(Atom::Variable(2));
        let term1 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![bool0.clone(), bool1.clone()],
        );
        let term2 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![bool1.clone(), bool2.clone()],
        );
        let mut u = test_unifier_bool(&ctx);

        u.assert_unify(Scope::LEFT, &term1, Scope::LEFT, &term2);
        let new1 = u.apply(Scope::LEFT, &term1);
        assert_eq!(format!("{}", new1), "g0(x0, x0)");
        let new2 = u.apply(Scope::LEFT, &term2);
        assert_eq!(format!("{}", new2), "g0(x0, x0)");
    }

    #[test]
    fn test_different_scope() {
        let ctx = test_ctx();
        let bool0 = Term::atom(Atom::Variable(0));
        let bool1 = Term::atom(Atom::Variable(1));
        let bool2 = Term::atom(Atom::Variable(2));
        let term1 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![bool0.clone(), bool1.clone()],
        );
        let term2 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![bool1.clone(), bool2.clone()],
        );
        let mut u = test_unifier_bool(&ctx);

        u.assert_unify(Scope::LEFT, &term1, Scope::RIGHT, &term2);
        let new1 = u.apply(Scope::LEFT, &term1);
        assert_eq!(format!("{}", new1), "g0(x0, x1)");
        let new2 = u.apply(Scope::RIGHT, &term2);
        assert_eq!(format!("{}", new2), "g0(x0, x1)");
    }

    #[test]
    fn test_unifying_functional_variable() {
        use crate::kernel::closed_type::ClosedType;
        // This test checks that a variable can unify with a constant in functional position.
        // Variable(1) should unify with GlobalConstant(3), both with type Empty -> Bool.
        let ctx = test_ctx();
        // g3 has type Empty -> Bool
        let empty_to_bool = ctx
            .symbol_table
            .get_closed_type(Symbol::GlobalConstant(3))
            .clone();

        let empty0 = Term::atom(Atom::Variable(0));
        let const_f_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(3)),
            vec![empty0.clone()],
        );
        let var_f_term = Term::new(Atom::Variable(1), vec![empty0.clone()]);

        // Set up a unifier where Variable(0) has EMPTY type and Variable(1) has Empty -> Bool type
        let mut u = Unifier::new(3, &ctx);
        // x0: EMPTY, x1: Empty -> Bool
        let local_ctx = LocalContext::from_closed_types(vec![ClosedType::empty(), empty_to_bool]);
        let local_ctx_ref: &'static LocalContext = Box::leak(Box::new(local_ctx));
        u.set_input_context(Scope::LEFT, local_ctx_ref);
        u.set_input_context(Scope::RIGHT, local_ctx_ref);
        u.set_output_var_closed_types(vec![ClosedType::empty(); 10]);
        u.assert_unify(Scope::LEFT, &const_f_term, Scope::RIGHT, &var_f_term);
    }

    #[test]
    fn test_nested_functional_unify() {
        use crate::kernel::closed_type::ClosedType;
        use crate::kernel::local_context::LocalContext;

        // Test: unify x0(x0(c5)) with c1(x0(x1))
        // x0 should map to c1, x1 should map to c5
        // x0 has type Bool -> Bool, x1 has type Bool
        // c1 is Bool -> Bool, c5 is Bool
        let ctx = test_ctx();
        let bool_to_bool = ctx
            .symbol_table
            .get_closed_type(Symbol::ScopedConstant(1))
            .clone();

        // Create local context where x0: Bool -> Bool, x1: Bool
        let local_ctx =
            LocalContext::from_closed_types(vec![bool_to_bool.clone(), ClosedType::bool()]);
        let local_ctx_ref: &'static LocalContext = Box::leak(Box::new(local_ctx));

        let c5 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(5)));
        let x1_var = Term::atom(Atom::Variable(1));

        // left_term = x0(x0(c5)) where x0 has type Bool -> Bool
        let inner = Term::new(Atom::Variable(0), vec![c5.clone()]);
        let left_term = Term::new(Atom::Variable(0), vec![inner]);

        // right_term = c1(x0(x1)) where c1: Bool -> Bool
        let x0_x1 = Term::new(Atom::Variable(0), vec![x1_var.clone()]);
        let right_term = Term::new(Atom::Symbol(Symbol::ScopedConstant(1)), vec![x0_x1]);

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, local_ctx_ref);
        u.set_input_context(Scope::RIGHT, local_ctx_ref);
        u.set_output_var_closed_types(vec![
            bool_to_bool,
            ClosedType::bool(),
            ClosedType::bool(),
            ClosedType::bool(),
            ClosedType::bool(),
        ]);

        u.assert_unify(Scope::LEFT, &left_term, Scope::RIGHT, &right_term);
        u.print();
        assert!(u.get_mapping(Scope::LEFT, 0).unwrap().to_string() == "c1");
        assert!(u.get_mapping(Scope::RIGHT, 0).unwrap().to_string() == "c1");
        assert!(u.get_mapping(Scope::RIGHT, 1).unwrap().to_string() == "c5");
    }

    // Tests that nested functional terms with function-typed variables can be unified.
    // Uses test_with_function_types where g1: Bool -> Bool.
    // We construct terms where x0 has type Bool -> Bool so x0(x0(x1)) is valid.
    #[test]
    fn test_nested_functional_superpose() {
        use crate::kernel::closed_type::ClosedType;
        let ctx = test_ctx();
        let bool_to_bool = ctx
            .symbol_table
            .get_closed_type(Symbol::GlobalConstant(1))
            .clone(); // g1: Bool -> Bool

        // Create local context where x0 has type Bool -> Bool, x1 has type Bool
        let lctx = LocalContext::from_closed_types(vec![bool_to_bool.clone(), ClosedType::bool()]);

        // Build terms: s = x0(x0(x1)) where x0: Bool -> Bool, x1: Bool
        // x0(x1) : Bool, x0(x0(x1)) : Bool
        let x1 = Term::atom(Atom::Variable(1));
        let x0_x1 = Term::new(Atom::Variable(0), vec![x1.clone()]);
        let s = Term::new(Atom::Variable(0), vec![x0_x1.clone()]);

        // u_subterm = g1(x0(x1))
        let u_subterm = Term::new(Atom::Symbol(Symbol::GlobalConstant(1)), vec![x0_x1.clone()]);

        // Test that s = x0(x0(x1)) unifies with u_subterm = g1(x0(x1))
        // This should succeed with x0 mapping to g1
        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(lctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(lctx.clone())));
        u.set_output_var_closed_types(vec![
            bool_to_bool,
            ClosedType::bool(),
            ClosedType::bool(),
            ClosedType::bool(),
        ]);

        u.assert_unify(Scope::LEFT, &s, Scope::RIGHT, &u_subterm);
        u.print();

        // Check that x0 in LEFT maps to g1
        let x0_mapping = u.get_mapping(Scope::LEFT, 0);
        assert!(x0_mapping.is_some(), "x0 should have a mapping");
        assert_eq!(x0_mapping.unwrap().to_string(), "g1", "x0 should map to g1");
    }

    // Tests higher-order partial application unification.
    // Uses test_with_function_types where:
    // - g0, c0: (Bool, Bool) -> Bool
    // - g1, c1: Bool -> Bool
    // - c5-c9: Bool
    #[test]
    fn test_higher_order_partial_application_unification() {
        use crate::kernel::closed_type::ClosedType;
        // We want to test unifying terms where a function variable gets bound to a partial application.
        // Using test_with_function_types:
        // - g0: (Bool, Bool) -> Bool
        // - Partial application g0(c5) gives Bool -> Bool
        //
        // We'll unify: x0(c6) with g0(c5, c6)
        // where x0 should map to g0(c5) (a partial application)

        let ctx = test_ctx();
        let bool_to_bool = ctx
            .symbol_table
            .get_closed_type(Symbol::GlobalConstant(1))
            .clone(); // g1: Bool -> Bool

        // c5, c6 are Bool constants
        let c5 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(5)));
        let c6 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(6)));

        // Left side: x0(c6) where x0: Bool -> Bool
        let left_local = LocalContext::from_closed_types(vec![bool_to_bool.clone()]);
        let left_term = Term::new(Atom::Variable(0), vec![c6.clone()]);

        // Right side: g0(c5, c6) : Bool
        // This is the full application
        let right_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![c5.clone(), c6.clone()],
        );

        // Right side has no variables
        let right_local = LocalContext::empty();

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(left_local)));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(right_local)));
        u.set_output_var_closed_types(vec![bool_to_bool, ClosedType::bool(), ClosedType::bool()]);

        let result = u.unify(Scope::LEFT, &left_term, Scope::RIGHT, &right_term);

        // This should succeed, with x0 mapping to g0(c5)
        assert!(result, "Should be able to unify x0(c6) with g0(c5, c6)");

        // Check that x0 maps to g0(c5)
        if result {
            let x0_mapping = u.get_mapping(Scope::LEFT, 0);
            assert!(x0_mapping.is_some(), "x0 should have a mapping");
            let mapping_str = x0_mapping.unwrap().to_string();
            assert_eq!(mapping_str, "g0(c5)", "x0 should map to g0(c5)");
        }
    }

    // Tests unification of terms that would be used in superposition.
    // This is a simplified version of the original test, focusing on unification correctness.
    // Uses test_with_function_types where g1: Bool -> Bool.
    #[test]
    fn test_original_superpose() {
        use crate::kernel::closed_type::ClosedType;
        let ctx = test_ctx();
        let bool_to_bool = ctx
            .symbol_table
            .get_closed_type(Symbol::GlobalConstant(1))
            .clone(); // g1: Bool -> Bool

        // Create local context where x0 has type Bool -> Bool, x1 has type Bool
        let lctx = LocalContext::from_closed_types(vec![bool_to_bool.clone(), ClosedType::bool()]);

        // Build terms: s = x0(x0(x1)) where x0: Bool -> Bool, x1: Bool
        let x0_x1 = Term::new(Atom::Variable(0), vec![Term::atom(Atom::Variable(1))]);
        let s = Term::new(Atom::Variable(0), vec![x0_x1.clone()]);

        // u_subterm = g1(x0(x1))
        let u_subterm = Term::new(Atom::Symbol(Symbol::GlobalConstant(1)), vec![x0_x1.clone()]);

        // Test that s = x0(x0(x1)) unifies with u_subterm = g1(x0(x1))
        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(lctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(lctx.clone())));
        u.set_output_var_closed_types(vec![
            bool_to_bool,
            ClosedType::bool(),
            ClosedType::bool(),
            ClosedType::bool(),
        ]);

        u.assert_unify(Scope::LEFT, &s, Scope::RIGHT, &u_subterm);
        u.print();

        // Now test that we can apply the unification to create a result
        let applied_s = u.apply(Scope::LEFT, &s);
        let applied_u = u.apply(Scope::RIGHT, &u_subterm);

        // After unification, both should have the same result
        // x0 -> g1, so s becomes g1(g1(x1)) and u_subterm becomes g1(g1(x1))
        assert_eq!(
            applied_s.to_string(),
            applied_u.to_string(),
            "After unification, both terms should apply to the same result"
        );
    }

    #[test]
    fn test_mutual_containment_invalid_1() {
        // Test: c0(x0, c0(x1, c1(x2))) should not unify with c0(c0(x2, x1), x0)
        // Using g0 which has type (Bool, Bool) -> Bool for c0-like behavior
        // Using g1 which has type Bool -> Bool for c1-like behavior
        let ctx = test_ctx();

        let x0 = Term::atom(Atom::Variable(0));
        let x1 = Term::atom(Atom::Variable(1));
        let x2 = Term::atom(Atom::Variable(2));

        // c1(x2) -> g1(x2)
        let g1_x2 = Term::new(Atom::Symbol(Symbol::GlobalConstant(1)), vec![x2.clone()]);
        // c0(x1, c1(x2)) -> g0(x1, g1(x2))
        let inner = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x1.clone(), g1_x2],
        );
        // c0(x0, c0(x1, c1(x2))) -> g0(x0, g0(x1, g1(x2)))
        let left_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x0.clone(), inner],
        );

        // c0(x2, x1) -> g0(x2, x1)
        let g0_x2_x1 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x2.clone(), x1.clone()],
        );
        // c0(c0(x2, x1), x0) -> g0(g0(x2, x1), x0)
        let right_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![g0_x2_x1, x0.clone()],
        );

        let mut u = test_unifier_bool(&ctx);
        let result = u.unify(Scope::LEFT, &left_term, Scope::LEFT, &right_term);
        assert!(!result, "Mutual containment should not unify");
    }

    #[test]
    fn test_mutual_containment_invalid_2() {
        // Test: c0(c0(x0, c1(x1)), x2) should not unify with c0(x2, c0(x1, x0))
        let ctx = test_ctx();

        let x0 = Term::atom(Atom::Variable(0));
        let x1 = Term::atom(Atom::Variable(1));
        let x2 = Term::atom(Atom::Variable(2));

        // c1(x1) -> g1(x1)
        let g1_x1 = Term::new(Atom::Symbol(Symbol::GlobalConstant(1)), vec![x1.clone()]);
        // c0(x0, c1(x1)) -> g0(x0, g1(x1))
        let inner_left = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x0.clone(), g1_x1],
        );
        // c0(c0(x0, c1(x1)), x2) -> g0(g0(x0, g1(x1)), x2)
        let left_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![inner_left, x2.clone()],
        );

        // c0(x1, x0) -> g0(x1, x0)
        let inner_right = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x1.clone(), x0.clone()],
        );
        // c0(x2, c0(x1, x0)) -> g0(x2, g0(x1, x0))
        let right_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x2.clone(), inner_right],
        );

        let mut u = test_unifier_bool(&ctx);
        let result = u.unify(Scope::LEFT, &left_term, Scope::LEFT, &right_term);
        assert!(!result, "Mutual containment should not unify");
    }

    #[test]
    fn test_recursive_reference_in_output() {
        // Test: g2(x0, x0) should not unify with g2(g2(g1(c0, x0), x0), g2(x1, x1))
        // g2 has type (Bool, Bool, Bool) -> Bool, but we need (Bool, Bool) -> Bool
        // So we use g0 instead
        let ctx = test_ctx();

        let x0 = Term::atom(Atom::Variable(0));
        let x1 = Term::atom(Atom::Variable(1));
        let c5 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(5))); // c5 is Bool

        // Left: g0(x0, x0)
        let left_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x0.clone(), x0.clone()],
        );

        // g1(c5) -> this doesn't fit since g1 has Bool -> Bool but we need a different structure
        // Original was g2(g2(g1(c0, x0), x0), g2(x1, x1)) which uses g1 with 2 args
        // Let's simplify: g0(g0(g0(c5, x0), x0), g0(x1, x1))
        let g0_c5_x0 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![c5.clone(), x0.clone()],
        );
        let g0_inner_x0 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![g0_c5_x0, x0.clone()],
        );
        let g0_x1_x1 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x1.clone(), x1.clone()],
        );
        let right_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![g0_inner_x0, g0_x1_x1],
        );

        let mut u = test_unifier_bool(&ctx);
        let result = u.unify(Scope::LEFT, &left_term, Scope::RIGHT, &right_term);
        assert!(!result, "Recursive reference should not unify");
    }

    #[test]
    fn test_initializing_with_variables_in_map() {
        use crate::kernel::closed_type::ClosedType;
        use crate::kernel::local_context::LocalContext;

        // Test initializing a unifier with pre-existing variable mappings
        let ctx = test_ctx();

        // Create a term for the initial mapping using only atomic synthetics
        // Use g2(x0, x1, s4) instead of s0(x0, x1, s4) since g2 has proper function type
        let x0 = Term::atom(Atom::Variable(0));
        let x1 = Term::atom(Atom::Variable(1));
        let s4 = Term::atom(Atom::Symbol(Symbol::Synthetic(4))); // BOOL type
        let g2_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(2)),
            vec![x0.clone(), x1.clone(), s4.clone()],
        );

        let mut initial_map = VariableMap::new();
        initial_map.set(0, g2_term);

        let local_ctx_ref: &'static LocalContext = LocalContext::test_bool_ref();
        let output_context = initial_map.build_output_context(local_ctx_ref);
        let (mut unifier, scope1) = Unifier::with_map(initial_map, &ctx, output_context);
        unifier.set_input_context(scope1, local_ctx_ref);
        let scope2 = unifier.add_scope();
        unifier.set_input_context(scope2, local_ctx_ref);
        let scope3 = unifier.add_scope();
        unifier.set_input_context(scope3, local_ctx_ref);
        unifier.set_output_var_closed_types(vec![ClosedType::bool(); 10]);

        // Unify g0(x0, x1) with g0(c5, x0)
        let c5 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(5)));
        let g0_x0_x1 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x0.clone(), x1.clone()],
        );
        let g0_c5_x0 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![c5.clone(), x0.clone()],
        );
        assert!(unifier.unify(scope2, &g0_x0_x1, scope3, &g0_c5_x0));

        // Unify g0(x2, x1) with g0(s4, x0)
        let x2 = Term::atom(Atom::Variable(2));
        let g0_x2_x1 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![x2.clone(), x1.clone()],
        );
        let g0_s4_x0 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![s4.clone(), x0.clone()],
        );
        assert!(unifier.unify(scope2, &g0_x2_x1, scope1, &g0_s4_x0));
    }
}
