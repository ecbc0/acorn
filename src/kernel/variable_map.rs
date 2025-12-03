use crate::kernel::aliases::{Clause, Literal, Term};
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::context::LocalContext;
use crate::kernel::fat_term::TypeId;
use crate::kernel::kernel_context::KernelContext;
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

    pub fn get_mapping(&self, i: AtomId) -> Option<&Term> {
        let i = i as usize;
        if i >= self.map.len() {
            None
        } else {
            self.map[i].as_ref()
        }
    }

    pub fn match_var(&mut self, var_id: AtomId, special_term: &Term) -> bool {
        let var_id = var_id as usize;
        if var_id >= self.map.len() {
            self.map.resize(var_id + 1, None);
        }
        match &self.map[var_id] {
            None => {
                self.map[var_id] = Some(special_term.clone());
                true
            }
            Some(general_term) => general_term == special_term,
        }
    }

    fn match_atoms(&mut self, atom_type: TypeId, general: &Atom, special: &Atom) -> bool {
        if let Atom::Variable(i) = general {
            self.match_var(*i, &Term::atom(atom_type, *special))
        } else {
            general == special
        }
    }

    pub fn match_terms(
        &mut self,
        general: &Term,
        special: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> bool {
        if general.get_term_type_with_context(local_context, kernel_context)
            != special.get_term_type_with_context(local_context, kernel_context)
        {
            return false;
        }

        // Handle the case where a general variable is being mapped to the whole term
        if let Some(i) = general.atomic_variable() {
            return self.match_var(i, special);
        }

        // These checks mean we won't catch higher-order functions whose head types don't match.
        if general.get_head_type_with_context(local_context, kernel_context)
            != special.get_head_type_with_context(local_context, kernel_context)
        {
            return false;
        }
        if general.args().len() != special.args().len() {
            return false;
        }

        if !self.match_atoms(
            general.get_head_type_with_context(local_context, kernel_context),
            &general.get_head_atom(),
            &special.get_head_atom(),
        ) {
            return false;
        }

        for (g, s) in general.args().iter().zip(special.args().iter()) {
            if !self.match_terms(g, s, local_context, kernel_context) {
                return false;
            }
        }
        true
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

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    fn specialize_term(
        &self,
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Term {
        let (head_type, head, mut args) = match *term.get_head_atom() {
            Atom::Variable(i) => {
                // Check if we have a mapping for this variable
                if let Some(replacement) = self.get_mapping(i) {
                    (
                        replacement.get_head_type_with_context(local_context, kernel_context),
                        *replacement.get_head_atom(),
                        replacement.args().to_vec(),
                    )
                } else {
                    // Keep the variable as-is if unmapped
                    (
                        term.get_head_type_with_context(local_context, kernel_context),
                        *term.get_head_atom(),
                        vec![],
                    )
                }
            }
            head => (
                term.get_head_type_with_context(local_context, kernel_context),
                head,
                vec![],
            ),
        };

        // Recurse on the arguments
        for arg in term.args() {
            args.push(self.specialize_term(arg, local_context, kernel_context));
        }

        Term::new(
            term.get_term_type_with_context(local_context, kernel_context),
            head_type,
            head,
            args,
        )
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    fn specialize_literal(
        &self,
        literal: &Literal,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Literal {
        Literal::new(
            literal.positive,
            self.specialize_term(&literal.left, local_context, kernel_context),
            self.specialize_term(&literal.right, local_context, kernel_context),
        )
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    pub fn specialize_clause(&self, clause: &Clause, kernel_context: &KernelContext) -> Clause {
        let local_context = clause.get_local_context();
        let literals = clause
            .literals
            .iter()
            .map(|lit| self.specialize_literal(lit, local_context, kernel_context))
            .collect();
        Clause { literals }
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
