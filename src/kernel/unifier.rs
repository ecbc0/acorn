use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::fat_clause::FatClause;
use crate::kernel::fat_literal::FatLiteral;
use crate::kernel::fat_term::{FatTerm, TypeId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
#[cfg(test)]
use crate::kernel::symbol::Symbol;
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
    term: &'a FatTerm,
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
    fn set_output_var_types(&mut self, types: Vec<TypeId>) {
        self.output_context = LocalContext::new(types);
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

    /// Creates a single-scope unifier.
    pub fn with_map(map: VariableMap, kernel_context: &'a KernelContext) -> (Unifier<'a>, Scope) {
        // Initialize the output map with enough blank entries for any variables in the initial map
        let mut output_map = VariableMap::new();
        // Also build output_context with the types of variables in the initial map
        let mut output_var_types: Vec<TypeId> = vec![];
        if let Some(max_var) = map.max_output_variable() {
            // Push blank entries up to and including the max variable index.
            for _ in 0..=max_var {
                output_map.push_none();
                // Default to TypeId 0; will be overwritten when we find the actual type
                output_var_types.push(TypeId::default());
            }
            // Extract actual types from the variables in the map
            for (_, term) in map.iter() {
                for (var_id, type_id) in term.collect_vars_embedded() {
                    let idx = var_id as usize;
                    if idx < output_var_types.len() {
                        output_var_types[idx] = type_id;
                    }
                }
            }
        }

        let unifier = Unifier {
            maps: vec![output_map, map],
            kernel_context,
            input_contexts: vec![None, None], // Output scope and one input scope
            output_context: LocalContext::new(output_var_types),
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
        self.input_contexts.push(None);
        scope
    }

    fn has_mapping(&self, scope: Scope, i: AtomId) -> bool {
        self.map(scope).has_mapping(i)
    }

    fn set_mapping(&mut self, scope: Scope, i: AtomId, term: FatTerm) {
        self.mut_map(scope).set(i, term);
    }

    fn get_mapping(&self, scope: Scope, i: AtomId) -> Option<&FatTerm> {
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
        term: &FatTerm,
        replacement: Option<Replacement>,
    ) -> FatTerm {
        if let Some(ref replacement) = replacement {
            if replacement.path.is_empty() {
                return self.apply(replacement.scope, replacement.term);
            }
        }

        // Extract term's type info upfront before any mutations
        // (For FatTerm, this just reads embedded fields, but we use _with_context for API consistency)
        let kernel_context = self.kernel_context;
        let term_type = {
            let local_context = self.get_local_context(scope);
            term.get_term_type_with_context(local_context, kernel_context)
        };
        let term_head_type = {
            let local_context = self.get_local_context(scope);
            term.get_head_type_with_context(local_context, kernel_context)
        };

        // First figure out what the head expands to, if it's a variable.
        // We track the head_type, head atom, and any args from the expansion separately.
        let (head_type, head, mut args) = match term.get_head_atom() {
            Atom::Variable(i) => {
                if !self.has_mapping(scope, *i) && scope != Scope::OUTPUT {
                    // We need to create a new variable to send this one to.
                    let var_id = self.maps[Scope::OUTPUT.get()].len() as AtomId;
                    self.maps[Scope::OUTPUT.get()].push_none();
                    // Track the type in output_context
                    self.output_context.var_types.push(term_head_type);
                    let new_var = FatTerm::new(
                        term_head_type,
                        term_head_type,
                        Atom::Variable(var_id),
                        vec![],
                    );
                    self.set_mapping(scope, *i, new_var);
                }

                match self.get_mapping(scope, *i) {
                    Some(mapped_head) => {
                        // The head of our initial term expands to a full term.
                        // mapped_head is in OUTPUT scope since mappings produce output terms.
                        let output_local = self.output_context();
                        (
                            mapped_head.get_head_type_with_context(output_local, kernel_context),
                            mapped_head.get_head_atom().clone(),
                            mapped_head.args().to_vec(),
                        )
                    }
                    None => {
                        // The head is an output variable with no mapping.
                        // Just leave it as it is.
                        assert!(scope == Scope::OUTPUT);
                        (term_head_type, term.get_head_atom().clone(), vec![])
                    }
                }
            }
            _head => (term_head_type, term.get_head_atom().clone(), vec![]),
        };

        // Recurse on the arguments and append them
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

        // Now construct the final term with correct types
        FatTerm::new(term_type, head_type, head, args)
    }

    pub fn apply(&mut self, scope: Scope, term: &FatTerm) -> FatTerm {
        self.apply_replace(scope, term, None)
    }

    /// Returns the resulting literal, and whether it was flipped.
    pub fn apply_to_literal(&mut self, scope: Scope, literal: &FatLiteral) -> (FatLiteral, bool) {
        let apply_left = self.apply(scope, &literal.left);
        let apply_right = self.apply(scope, &literal.right);
        FatLiteral::new_with_flip(literal.positive, apply_left, apply_right)
    }

    // Replace variable i in the output scope with the given term (which is also in the output scope).
    // If they're both variables, keep the one with the lower id.
    // Returns whether this succeeded.
    // It fails if this would require making a variable self-nesting.
    fn remap(&mut self, id: AtomId, term: &FatTerm) -> bool {
        if let Some(other_id) = term.atomic_variable() {
            if other_id > id {
                // Let's keep this id and remap the other one instead.
                // Since term is an atomic variable, create a new variable term with the lower id.
                // term is in OUTPUT scope
                let term_type =
                    term.get_term_type_with_context(self.output_context(), self.kernel_context);
                let new_term = FatTerm::new_variable(term_type, id);
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
        term: &FatTerm,
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
            return self.unify_internal(Scope::OUTPUT, &existing, Scope::OUTPUT, term);
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
            return self.unify_variable(scope1, *i, scope2, &FatTerm::atom(atom_type, *atom2));
        }
        if let Atom::Variable(i) = atom2 {
            return self.unify_variable(scope2, *i, scope1, &FatTerm::atom(atom_type, *atom1));
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
        var_term: &FatTerm,
        var_scope: Scope,
        full_term: &FatTerm,
        full_scope: Scope,
    ) -> Option<bool> {
        // Check if var_term has a variable head with arguments
        if let Atom::Variable(var_id) = *var_term.get_head_atom() {
            let var_args_len = var_term.args().len();
            let full_args_len = full_term.args().len();

            if var_args_len >= 1 && full_args_len > var_args_len {
                // We want to unify x0(arg1, ..., argN) with f(a1, ..., aM) where M > N
                // This means x0 should map to f(a1, ..., a(M-N))
                // and each argi should unify with a(M-N+i)

                // Build the partial application: first (M-N) args of full_term
                let num_partial_args = full_args_len - var_args_len;
                let partial_args = full_term.args()[0..num_partial_args].to_vec();

                // Create the partial application term
                // Use the head_type of var_term (the variable's type) as the term_type
                let var_local = self.get_local_context(var_scope);
                let full_local = self.get_local_context(full_scope);
                let partial = FatTerm::new(
                    var_term.get_head_type_with_context(var_local, self.kernel_context),
                    full_term.get_head_type_with_context(full_local, self.kernel_context),
                    *full_term.get_head_atom(),
                    partial_args,
                );

                // Unify the variable with the partial application
                if !self.unify_variable(var_scope, var_id, full_scope, &partial) {
                    return Some(false);
                }

                // Unify each var_term argument with the corresponding full_term argument
                for i in 0..var_args_len {
                    if !self.unify_internal(
                        var_scope,
                        &var_term.args()[i],
                        full_scope,
                        &full_term.args()[num_partial_args + i],
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
    pub fn unify(
        &mut self,
        scope1: Scope,
        term1: &FatTerm,
        scope2: Scope,
        term2: &FatTerm,
    ) -> bool {
        if scope1 == Scope::OUTPUT || scope2 == Scope::OUTPUT {
            panic!("Cannot call unify with output scope - the unifier manages output variables internally");
        }
        self.unify_internal(scope1, term1, scope2, term2)
    }

    // Internal unification implementation
    fn unify_internal(
        &mut self,
        scope1: Scope,
        term1: &FatTerm,
        scope2: Scope,
        term2: &FatTerm,
    ) -> bool {
        let local1 = self.get_local_context(scope1);
        let local2 = self.get_local_context(scope2);
        let kc = self.kernel_context;

        if term1.get_term_type_with_context(local1, kc)
            != term2.get_term_type_with_context(local2, kc)
        {
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

        // Re-get local contexts since we may have modified them above
        let local1 = self.get_local_context(scope1);
        let local2 = self.get_local_context(scope2);

        // These checks mean we won't unify higher-order functions whose head types don't match.
        if term1.get_head_type_with_context(local1, kc)
            != term2.get_head_type_with_context(local2, kc)
        {
            return false;
        }
        if term1.args().len() != term2.args().len() {
            return false;
        }

        if !self.unify_atoms(
            term1.get_head_type_with_context(local1, kc),
            scope1,
            &term1.get_head_atom(),
            scope2,
            &term2.get_head_atom(),
        ) {
            return false;
        }

        for (a1, a2) in term1.args().iter().zip(term2.args().iter()) {
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
        literal1: &FatLiteral,
        scope2: Scope,
        literal2: &FatLiteral,
        flipped: bool,
    ) -> bool {
        if flipped {
            // If we're flipped, swap the literals.
            self.unify_internal(scope1, &literal1.right, scope2, &literal2.left)
                && self.unify_internal(scope1, &literal1.left, scope2, &literal2.right)
        } else {
            // If we're not flipped, keep the literals as they are.
            self.unify_internal(scope1, &literal1.left, scope2, &literal2.left)
                && self.unify_internal(scope1, &literal1.right, scope2, &literal2.right)
        }
    }

    /// Tries to unify a left clause and a right clause.
    /// Does not reorder anything.
    pub fn unify_clauses(
        left: &FatClause,
        right: &FatClause,
        kernel_context: &KernelContext,
    ) -> bool {
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

    pub fn assert_unify(&mut self, scope1: Scope, term1: &FatTerm, scope2: Scope, term2: &FatTerm) {
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
        let term1 = FatTerm::parse(str1);
        let term2 = FatTerm::parse(str2);
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
        t: &FatTerm,
        path: &[usize],
        res_literal: &FatLiteral,
        res_forwards: bool,
    ) -> FatLiteral {
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
        FatLiteral::new(res_literal.positive, unified_u, unified_v)
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
        t: &FatTerm,
        pm_clause: &FatClause,
        pm_literal_index: usize,
        path: &[usize],
        res_clause: &FatClause,
        res_literal_index: usize,
        res_forwards: bool,
    ) -> Vec<FatLiteral> {
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
    use crate::kernel::fat_term::{BOOL, EMPTY};

    use super::*;

    fn bool_fn(head: Atom, head_type: TypeId, args: Vec<FatTerm>) -> FatTerm {
        FatTerm::new(BOOL, head_type, head, args)
    }

    /// Creates a test unifier with LEFT and RIGHT contexts set to an empty context.
    /// Creates a test KernelContext suitable for tests using GlobalConstant symbols.
    fn test_ctx() -> KernelContext {
        KernelContext::test_with_constants(10, 10)
    }

    /// Creates a test unifier with EMPTY types for variables.
    /// Use this for tests that use FatTerm::parse() which creates EMPTY types.
    fn test_unifier<'a>(kernel_context: &'a KernelContext) -> Unifier<'a> {
        use crate::kernel::local_context::LocalContext;
        let mut u = Unifier::new(3, kernel_context);
        u.set_input_context(Scope::LEFT, LocalContext::test_empty_ref());
        u.set_input_context(Scope::RIGHT, LocalContext::test_empty_ref());
        u.set_output_var_types(vec![EMPTY; 10]);
        u
    }

    /// Creates a test unifier with BOOL types for variables.
    /// Use this for tests that explicitly construct terms with BOOL types.
    fn test_unifier_bool<'a>(kernel_context: &'a KernelContext) -> Unifier<'a> {
        use crate::kernel::local_context::LocalContext;
        let mut u = Unifier::new(3, kernel_context);
        u.set_input_context(Scope::LEFT, LocalContext::test_bool_ref());
        u.set_input_context(Scope::RIGHT, LocalContext::test_bool_ref());
        u.set_output_var_types(vec![BOOL; 10]);
        u
    }

    #[test]
    fn test_unifying_variables() {
        let bool0 = FatTerm::atom(BOOL, Atom::Variable(0));
        let bool1 = FatTerm::atom(BOOL, Atom::Variable(1));
        let bool2 = FatTerm::atom(BOOL, Atom::Variable(2));
        let fterm = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            EMPTY, // GlobalConstant head type is EMPTY from test_ctx
            vec![bool0.clone(), bool1.clone()],
        );
        let ctx = test_ctx();
        let mut u = test_unifier_bool(&ctx);

        // Replace x0 with x1 and x1 with x2.
        assert!(u.unify_variable(Scope::LEFT, 0, Scope::OUTPUT, &bool1));
        assert!(u.unify_variable(Scope::LEFT, 1, Scope::OUTPUT, &bool2));
        let term = u.apply(Scope::LEFT, &fterm);
        assert_eq!(format!("{}", term), "g0(x1, x2)");
    }

    #[test]
    fn test_same_scope() {
        let bool0 = FatTerm::atom(BOOL, Atom::Variable(0));
        let bool1 = FatTerm::atom(BOOL, Atom::Variable(1));
        let bool2 = FatTerm::atom(BOOL, Atom::Variable(2));
        let term1 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            EMPTY, // GlobalConstant head type is EMPTY from test_ctx
            vec![bool0.clone(), bool1.clone()],
        );
        let term2 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            EMPTY, // GlobalConstant head type is EMPTY from test_ctx
            vec![bool1.clone(), bool2.clone()],
        );
        let ctx = test_ctx();
        let mut u = test_unifier_bool(&ctx);

        u.assert_unify(Scope::LEFT, &term1, Scope::LEFT, &term2);
        let new1 = u.apply(Scope::LEFT, &term1);
        assert_eq!(format!("{}", new1), "g0(x0, x0)");
        let new2 = u.apply(Scope::LEFT, &term2);
        assert_eq!(format!("{}", new2), "g0(x0, x0)");
    }

    #[test]
    fn test_different_scope() {
        let bool0 = FatTerm::atom(BOOL, Atom::Variable(0));
        let bool1 = FatTerm::atom(BOOL, Atom::Variable(1));
        let bool2 = FatTerm::atom(BOOL, Atom::Variable(2));
        let term1 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            EMPTY, // GlobalConstant head type is EMPTY from test_ctx
            vec![bool0.clone(), bool1.clone()],
        );
        let term2 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(0)),
            EMPTY, // GlobalConstant head type is EMPTY from test_ctx
            vec![bool1.clone(), bool2.clone()],
        );
        let ctx = test_ctx();
        let mut u = test_unifier_bool(&ctx);

        u.assert_unify(Scope::LEFT, &term1, Scope::RIGHT, &term2);
        let new1 = u.apply(Scope::LEFT, &term1);
        assert_eq!(format!("{}", new1), "g0(x0, x1)");
        let new2 = u.apply(Scope::RIGHT, &term2);
        assert_eq!(format!("{}", new2), "g0(x0, x1)");
    }

    #[test]
    fn test_unifying_functional_variable() {
        // This test checks that a variable can unify with a constant in functional position.
        // Variable(1) should unify with GlobalConstant(0), both with type EMPTY.
        let empty0 = FatTerm::atom(EMPTY, Atom::Variable(0));
        let const_f_term = FatTerm::new(
            BOOL,
            EMPTY, // GlobalConstant head type is EMPTY from test_ctx
            Atom::Symbol(Symbol::GlobalConstant(0)),
            vec![empty0.clone()],
        );
        let var_f_term = FatTerm::new(
            BOOL,
            EMPTY, // Variable head type - must match GlobalConstant for unification
            Atom::Variable(1),
            vec![empty0.clone()],
        );

        let ctx = test_ctx();
        let mut u = test_unifier(&ctx); // Use EMPTY types for variables
        u.assert_unify(Scope::LEFT, &const_f_term, Scope::RIGHT, &var_f_term);
    }

    #[test]
    fn test_nested_functional_unify() {
        let left_term = FatTerm::parse("x0(x0(c0))");
        let right_term = FatTerm::parse("c1(x0(x1))");
        let ctx = test_ctx();
        let mut u = test_unifier(&ctx);
        u.assert_unify(Scope::LEFT, &left_term, Scope::RIGHT, &right_term);
        u.print();
        assert!(u.get_mapping(Scope::LEFT, 0).unwrap().to_string() == "c1");
        assert!(u.get_mapping(Scope::RIGHT, 0).unwrap().to_string() == "c1");
        assert!(u.get_mapping(Scope::RIGHT, 1).unwrap().to_string() == "c0");
    }

    #[test]
    fn test_nested_functional_superpose() {
        let s = FatTerm::parse("x0(x0(x1))");
        let u_subterm = FatTerm::parse("c1(x0(x1))");
        let t = FatTerm::parse("c2(x0, x1, c1(c1(c0)))");
        let pm_clause = FatClause::parse("c2(x0, x1, c1(c1(c0))) = x0(x0(x1))");
        let target_path = &[0];
        let resolution_clause =
            FatClause::parse("c1(c1(x0(x1))) != c1(x2(x3)) or c1(x0(x1)) = x2(x3)");
        let ctx = test_ctx();
        let mut u = test_unifier(&ctx);
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
        let x0_var = FatTerm::atom(TypeId::new(11), Atom::Variable(0));
        let x1_var = FatTerm::atom(TypeId::new(2), Atom::Variable(1));

        // s5 is a skolem function that takes two arguments
        let s5_left = FatTerm::new(
            TypeId::new(4),
            TypeId::new(14),
            Atom::Symbol(Symbol::Synthetic(5)),
            vec![x0_var.clone(), x1_var.clone()],
        );

        // Left side: x0(s5(x0, x1))
        let left_term = FatTerm::new(
            TypeId::new(4),
            TypeId::new(11),
            Atom::Variable(0),
            vec![s5_left],
        );

        // Right side: m2(c0, s5(m2(c0), x0))
        let c0 = FatTerm::atom(TypeId::new(2), Atom::Symbol(Symbol::ScopedConstant(0)));
        let m2_c0 = FatTerm::new(
            TypeId::new(11),
            TypeId::new(10),
            Atom::Symbol(Symbol::Monomorph(2)),
            vec![c0.clone()],
        );

        let s5_right = FatTerm::new(
            TypeId::new(4),
            TypeId::new(14),
            Atom::Symbol(Symbol::Synthetic(5)),
            vec![
                m2_c0.clone(),
                FatTerm::atom(TypeId::new(2), Atom::Variable(0)),
            ],
        );

        let right_term = FatTerm::new(
            TypeId::new(4),
            TypeId::new(10),
            Atom::Symbol(Symbol::Monomorph(2)),
            vec![c0.clone(), s5_right],
        );

        // Create custom kernel context with proper types for:
        // - ScopedConstant(0): type 2
        // - Monomorph(2): type 10 (need indices 0, 1, 2)
        // - Synthetic(5): type 14 (need indices 0-5)
        let ctx = KernelContext::test_with_all_types(
            &[TypeId::new(2)],                                     // scoped c0
            &[],                                                   // no globals
            &[EMPTY, EMPTY, TypeId::new(10)],                      // monomorphs m0, m1, m2
            &[EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, TypeId::new(14)], // synthetics s0-s5
        );

        // Try to unify these terms
        // Create custom contexts for LEFT (x0: type 11, x1: type 2) and RIGHT (x0: type 2)
        let mut u = Unifier::new(3, &ctx);
        let left_local = LocalContext::with_types(vec![TypeId::new(11), TypeId::new(2)]);
        let right_local = LocalContext::with_types(vec![TypeId::new(2)]);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(left_local)));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(right_local)));
        // Don't pre-populate output_context - let the unifier create output variables dynamically
        // with the correct types from the input terms.

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
        let s = FatTerm::parse("x0(x0(x1))");
        let u_subterm = FatTerm::parse("c1(x0(x1))");
        let t = FatTerm::parse("c2(x0, x1, c1(c1(c0)))");
        let pm_clause = FatClause::parse("c2(x0, x1, c1(c1(c0))) = x0(x0(x1))");
        let target_path = &[0];
        let resolution_clause =
            FatClause::parse("c1(c1(x0(x1))) != c1(x2(x3)) or c1(x0(x1)) = x2(x3)");
        let ctx = test_ctx();
        let mut u = test_unifier(&ctx);
        u.assert_unify(Scope::LEFT, &s, Scope::RIGHT, &u_subterm);
        u.print();
        let literals =
            u.superpose_clauses(&t, &pm_clause, 0, target_path, &resolution_clause, 0, true);
        let new_clause = FatClause::new_without_context(literals);
        assert!(
            new_clause.to_string()
                == "c1(c2(c1, x0, c1(c1(c0)))) != c1(x1(x2)) or c1(c1(x0)) = x1(x2)"
        );
    }

    #[test]
    fn test_mutual_containment_invalid_1() {
        let ctx = test_ctx();
        let mut u = test_unifier(&ctx);
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
        let ctx = test_ctx();
        let mut u = test_unifier(&ctx);
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
        let ctx = test_ctx();
        let mut u = test_unifier(&ctx);
        u.unify_str(
            Scope::LEFT,
            "g2(x0, x0)",
            Scope::RIGHT,
            "g2(g2(g1(c0, x0), x0), g2(x1, x1))",
            false,
        );
    }

    #[test]
    fn test_initializing_with_variables_in_map() {
        use crate::kernel::local_context::LocalContext;
        let ctx = test_ctx();
        let mut initial_map = VariableMap::new();
        initial_map.set(0, FatTerm::parse("s0(x0, x1, s4)"));
        let (mut unifier, scope1) = Unifier::with_map(initial_map, &ctx);
        // Set contexts for all scopes
        unifier.set_input_context(scope1, LocalContext::test_empty_ref());
        let scope2 = unifier.add_scope();
        unifier.set_input_context(scope2, LocalContext::test_empty_ref());
        let scope3 = unifier.add_scope();
        unifier.set_input_context(scope3, LocalContext::test_empty_ref());
        // Pre-populate output context with enough types for all output variables
        unifier.set_output_var_types(vec![EMPTY; 10]);

        unifier.unify_str(scope2, "g6(x0, x1)", scope3, "g6(c1, x0)", true);
        unifier.unify_str(scope2, "g0(x2, x1)", scope1, "g0(s4, x0)", true);
    }
}
