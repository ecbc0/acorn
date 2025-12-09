use crate::kernel::aliases::{Clause, Literal, Term};
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::closed_type::ClosedType;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::TermRef;
use crate::kernel::types::{GroundTypeId, TypeId, EMPTY};
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
    /// TODO: This uses EMPTY as a fallback ground type, which may not be correct for all contexts.
    pub fn build_output_context(&self, input_context: &LocalContext) -> LocalContext {
        let empty_type = ClosedType::ground(GroundTypeId::new(EMPTY.as_u16()));
        let mut var_closed_types: Vec<Option<ClosedType>> = vec![];
        for opt_term in &self.map {
            if let Some(term) = opt_term {
                for (var_id, closed_type) in term.collect_vars_closed(input_context) {
                    let idx = var_id as usize;
                    if idx >= var_closed_types.len() {
                        var_closed_types.resize(idx + 1, None);
                    }
                    var_closed_types[idx] = Some(closed_type);
                }
            }
        }
        LocalContext::from_closed_types(
            var_closed_types
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

    fn match_atoms(&mut self, _atom_type: TypeId, general: &Atom, special: &Atom) -> bool {
        if let Atom::Variable(i) = general {
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
        if general.get_term_type_with_context(general_context, kernel_context)
            != special.get_term_type_with_context(special_context, kernel_context)
        {
            return false;
        }

        // Handle the case where a general variable is being mapped to the whole term
        if let Some(i) = general.atomic_variable() {
            return self.match_var(i, special);
        }

        // These checks mean we won't catch higher-order functions whose head types don't match.
        if general.get_head_type_with_context(general_context, kernel_context)
            != special.get_head_type_with_context(special_context, kernel_context)
        {
            return false;
        }
        if general.num_args() != special.num_args() {
            return false;
        }

        if !self.match_atoms(
            general.get_head_type_with_context(general_context, kernel_context),
            general.get_head_atom(),
            special.get_head_atom(),
        ) {
            return false;
        }

        for (g, s) in general.iter_args().zip(special.iter_args()) {
            if !self.match_terms(g, s, general_context, special_context, kernel_context) {
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
    /// input_context is for the input term, output_context is for replacement terms in the map.
    fn specialize_term(
        &self,
        term: TermRef,
        input_context: &LocalContext,
        output_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Term {
        let (head, mut args) = match *term.get_head_atom() {
            Atom::Variable(i) => {
                // Check if we have a mapping for this variable
                if let Some(replacement) = self.get_mapping(i) {
                    (*replacement.get_head_atom(), replacement.args())
                } else {
                    // Keep the variable as-is if unmapped
                    (*term.get_head_atom(), vec![])
                }
            }
            head => (head, vec![]),
        };

        // Recurse on the arguments
        for arg in term.iter_args() {
            args.push(self.specialize_term(arg, input_context, output_context, kernel_context));
        }

        Term::new(head, args)
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
                if let Some(closed_type) = input_context.get_var_closed_type(i) {
                    output_context.set_closed_type(i, closed_type.clone());
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
