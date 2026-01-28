use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::{Decomposition, Term, TermRef};
use std::fmt;

// A VariableMap maintains a mapping from variables to terms, allowing us to turn a more general term
// into a more specific one by substituting variables.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct VariableMap {
    map: Vec<Option<Term>>,
}

impl VariableMap {
    pub fn new() -> VariableMap {
        VariableMap { map: Vec::new() }
    }

    /// Returns the maximum variable index in any of the mapped terms, or None if there are no variables.
    pub fn max_output_variable(&self) -> Option<AtomId> {
        let mut max: Option<AtomId> = None;
        for opt_term in &self.map {
            if let Some(term) = opt_term {
                if let Some(term_max) = term.max_variable() {
                    max = Some(match max {
                        None => term_max,
                        Some(current_max) => current_max.max(term_max),
                    });
                }
            }
        }
        max
    }

    /// Builds a LocalContext from all the variables in the replacement terms.
    /// We need the input_context to look up variable types.
    ///
    /// Note: The returned context may have gaps filled with EMPTY placeholders.
    /// This is because replacement terms may contain non-sequential variable IDs
    /// (e.g., x3 without x0, x1, x2). The context uses index-based lookup, so we
    /// need entries at all indices up to the max variable ID.
    /// These placeholders are safe because:
    /// 1. They're only used temporarily in unnormalized clauses
    /// 2. When the clause is normalized, variable IDs become sequential
    /// 3. The remap operation only keeps entries for actual variables
    pub fn build_output_context(&self, input_context: &LocalContext) -> LocalContext {
        let empty_type = Term::empty_type();
        let mut var_types: Vec<Option<Term>> = vec![];
        for opt_term in &self.map {
            if let Some(term) = opt_term {
                for (var_id, var_type) in term.collect_vars(input_context) {
                    let idx = var_id as usize;
                    if idx >= var_types.len() {
                        var_types.resize(idx + 1, None);
                    }
                    var_types[idx] = Some(var_type);
                }
            }
        }
        LocalContext::from_types(
            var_types
                .into_iter()
                .map(|t| t.unwrap_or_else(|| empty_type.clone()))
                .collect(),
        )
    }

    pub fn get_mapping(&self, i: AtomId) -> Option<&Term> {
        let i = i as usize;
        if i >= self.map.len() {
            None
        } else {
            self.map[i].as_ref()
        }
    }

    pub fn match_var(&mut self, var_id: AtomId, special_term: TermRef) -> bool {
        let var_id = var_id as usize;
        if var_id >= self.map.len() {
            self.map.resize(var_id + 1, None);
        }
        match &self.map[var_id] {
            None => {
                self.map[var_id] = Some(special_term.to_owned());
                true
            }
            Some(general_term) => general_term.as_ref() == special_term,
        }
    }

    fn match_atoms(&mut self, general: &Atom, special: &Atom) -> bool {
        if let Atom::FreeVariable(i) = general {
            self.match_var(*i, Term::atom(*special).as_ref())
        } else {
            general == special
        }
    }

    pub fn match_terms(
        &mut self,
        general: TermRef,
        special: TermRef,
        general_context: &LocalContext,
        special_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> bool {
        // Type checking is only needed when matching a variable to a term.
        // For other cases (atom vs atom, application vs application), if the
        // subterms match structurally, their types are guaranteed to match.
        match (general.decompose(), special.decompose()) {
            (Decomposition::Atom(Atom::FreeVariable(i)), _) => {
                // When matching a variable, we must verify type compatibility.
                // Get the variable's type directly from the context (cheap lookup)
                // rather than computing it via get_type_with_context.
                let var_type = general_context.get_var_type(*i as usize).unwrap();
                let special_type = special.get_type_with_context(special_context, kernel_context);
                if var_type != &special_type {
                    return false;
                }
                self.match_var(*i, special)
            }
            (Decomposition::Atom(g_atom), Decomposition::Atom(s_atom)) => {
                self.match_atoms(g_atom, s_atom)
            }
            (
                Decomposition::Application(g_func, g_arg),
                Decomposition::Application(s_func, s_arg),
            ) => {
                self.match_terms(
                    g_func,
                    s_func,
                    general_context,
                    special_context,
                    kernel_context,
                ) && self.match_terms(
                    g_arg,
                    s_arg,
                    general_context,
                    special_context,
                    kernel_context,
                )
            }
            // Atom vs Application mismatch
            _ => false,
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn get(&self, i: usize) -> Option<&Term> {
        self.map.get(i).and_then(|opt| opt.as_ref())
    }

    pub fn set(&mut self, i: AtomId, term: Term) {
        let i = i as usize;
        if i >= self.map.len() {
            self.map.resize(i + 1, None);
        }
        self.map[i] = Some(term);
    }

    pub fn has_mapping(&self, i: AtomId) -> bool {
        let i = i as usize;
        i < self.map.len() && self.map[i].is_some()
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, &Term)> {
        self.map
            .iter()
            .enumerate()
            .filter_map(|(i, opt)| opt.as_ref().map(|term| (i, term)))
    }

    pub fn apply_to_all<F>(&mut self, mut f: F)
    where
        F: FnMut(&Term) -> Term,
    {
        for opt in &mut self.map {
            if let Some(term) = opt {
                *term = f(term);
            }
        }
    }

    pub fn push_none(&mut self) {
        self.map.push(None);
    }

    /// Compose this map with another.
    /// self maps: A vars → terms with B vars (B types in self_context)
    /// other maps: B vars → terms with C vars (C types in other_context)
    /// Result: A vars → terms with C vars
    ///
    /// This is used during proof reconstruction to compose:
    /// - premise_var_map (premise vars → output vars) with
    /// - conclusion_map (output vars → concrete terms)
    /// to get premise vars → concrete terms.
    pub fn compose(
        &self,
        self_context: &LocalContext,
        other: &VariableMap,
        other_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> VariableMap {
        let mut result = VariableMap::new();
        for (var_id, term) in self.iter() {
            let specialized =
                other.specialize_term(term.as_ref(), self_context, other_context, kernel_context);
            result.set(var_id as AtomId, specialized);
        }
        result
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    /// input_context is for the input term, output_context is for replacement terms in the map.
    fn specialize_term(
        &self,
        term: TermRef,
        input_context: &LocalContext,
        output_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Term {
        match term.decompose() {
            Decomposition::Atom(Atom::FreeVariable(i)) => {
                // Check if we have a mapping for this variable
                if let Some(replacement) = self.get_mapping(*i) {
                    replacement.clone()
                } else {
                    // Keep the variable as-is if unmapped
                    term.to_owned()
                }
            }
            Decomposition::Atom(_) => term.to_owned(),
            Decomposition::Application(func, arg) => {
                let specialized_func =
                    self.specialize_term(func, input_context, output_context, kernel_context);
                let specialized_arg =
                    self.specialize_term(arg, input_context, output_context, kernel_context);
                specialized_func.apply(&[specialized_arg])
            }
            Decomposition::Pi(input, output) => {
                let specialized_input =
                    self.specialize_term(input, input_context, output_context, kernel_context);
                let specialized_output =
                    self.specialize_term(output, input_context, output_context, kernel_context);
                Term::pi(specialized_input, specialized_output)
            }
        }
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    /// input_context is for the input literal, output_context is for replacement terms in the map.
    fn specialize_literal(
        &self,
        literal: &Literal,
        input_context: &LocalContext,
        output_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Literal {
        Literal::new(
            literal.positive,
            self.specialize_term(
                literal.left.as_ref(),
                input_context,
                output_context,
                kernel_context,
            ),
            self.specialize_term(
                literal.right.as_ref(),
                input_context,
                output_context,
                kernel_context,
            ),
        )
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    pub fn specialize_clause(&self, clause: &Clause, kernel_context: &KernelContext) -> Clause {
        let input_context = clause.get_local_context();
        let output_context = self.build_output_context(input_context);
        let literals = clause
            .literals
            .iter()
            .map(|lit| self.specialize_literal(lit, input_context, &output_context, kernel_context))
            .collect();
        Clause::from_literals_unnormalized(literals, &output_context)
    }

    /// Like specialize_clause, but uses a separate context for looking up types in replacement terms.
    /// This is needed when the VariableMap's replacement terms were created with
    /// variables from a different context than the clause being specialized.
    pub fn specialize_clause_with_replacement_context(
        &self,
        clause: &Clause,
        replacement_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Clause {
        let input_context = clause.get_local_context();
        // Build output context from replacement terms
        let mut output_context = self.build_output_context(replacement_context);
        // Also need to include unmapped variables from the input clause
        // These keep their original types from the input context
        for i in 0..input_context.len() {
            if self.get_mapping(i as AtomId).is_none() {
                // This variable is unmapped, so it will remain in the output
                if let Some(var_type) = input_context.get_var_type(i) {
                    output_context.set_type(i, var_type.clone());
                }
            }
        }
        let literals = clause
            .literals
            .iter()
            .map(|lit| self.specialize_literal(lit, input_context, &output_context, kernel_context))
            .collect();
        Clause::from_literals_unnormalized(literals, &output_context)
    }

    pub fn output_has_any_variable(&self) -> bool {
        for term in &self.map {
            if let Some(term) = term {
                if term.has_any_variable() {
                    return true;
                }
            }
        }
        false
    }
}

impl fmt::Display for VariableMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        let mut first = true;
        for (i, term) in self.iter() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "x{} -> {}", i, term)?;
            first = false;
        }
        write!(f, ")")
    }
}
