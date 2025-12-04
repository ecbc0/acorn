use serde::{Deserialize, Serialize};
use std::fmt;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::fat_term::{TypeId, BOOL, EMPTY};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;

/// A component of a ThinTerm in its flattened representation.
/// Either a Composite node or an Atom leaf node.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum ThinTermComponent {
    /// Indicates a composite argument with the given span (total number of components).
    /// The span includes this Composite marker itself, the head, and all arguments recursively.
    /// To skip over this entire subterm: index += span
    /// To enter this subterm (process the head): index += 1
    Composite { span: u16 },

    /// A leaf atom in the term tree.
    Atom(Atom),
}

/// A borrowed reference to a thin term - wraps a slice of components.
/// This is the borrowed equivalent of ThinTerm, similar to how &str relates to String.
/// Most operations work on ThinTermRef to avoid unnecessary allocations.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ThinTermRef<'a> {
    components: &'a [ThinTermComponent],
}

impl<'a> ThinTermRef<'a> {
    /// Create a ThinTermRef from a slice of components.
    pub fn new(components: &'a [ThinTermComponent]) -> ThinTermRef<'a> {
        ThinTermRef { components }
    }

    /// Convert this reference to an owned ThinTerm by cloning the components.
    pub fn to_owned(&self) -> ThinTerm {
        ThinTerm {
            components: self.components.to_vec(),
        }
    }

    /// Get the head atom of this term.
    /// The head is always the first component (or first after Composite marker).
    pub fn get_head_atom(&self) -> &Atom {
        match &self.components[0] {
            ThinTermComponent::Atom(atom) => atom,
            ThinTermComponent::Composite { .. } => {
                panic!("ThinTerm should not start with Composite marker")
            }
        }
    }

    /// Check if this term is atomic (no arguments).
    pub fn is_atomic(&self) -> bool {
        self.components.len() == 1
    }

    /// Check if this term is the boolean constant "true".
    pub fn is_true(&self) -> bool {
        matches!(self.get_head_atom(), Atom::True)
    }

    /// Check if this term is a variable (atomic and head is a variable).
    pub fn is_variable(&self) -> bool {
        self.is_atomic() && self.get_head_atom().is_variable()
    }

    /// If this is an atomic variable, return its index.
    pub fn atomic_variable(&self) -> Option<AtomId> {
        if !self.is_atomic() {
            return None;
        }
        match self.get_head_atom() {
            Atom::Variable(i) => Some(*i),
            _ => None,
        }
    }

    /// Check if this term contains a variable with the given index anywhere.
    pub fn has_variable(&self, index: AtomId) -> bool {
        for component in self.components {
            if let ThinTermComponent::Atom(Atom::Variable(i)) = component {
                if *i == index {
                    return true;
                }
            }
        }
        false
    }

    /// Check if this term contains any variables.
    pub fn has_any_variable(&self) -> bool {
        for component in self.components {
            if let ThinTermComponent::Atom(atom) = component {
                if atom.is_variable() {
                    return true;
                }
            }
        }
        false
    }

    /// Check if this term contains any local constants.
    pub fn has_scoped_constant(&self) -> bool {
        for component in self.components {
            if let ThinTermComponent::Atom(atom) = component {
                if atom.is_scoped_constant() {
                    return true;
                }
            }
        }
        false
    }

    /// Check if this term contains any synthetic atoms.
    pub fn has_synthetic(&self) -> bool {
        use crate::kernel::symbol::Symbol;
        for component in self.components {
            if let ThinTermComponent::Atom(Atom::Symbol(Symbol::Synthetic(_))) = component {
                return true;
            }
        }
        false
    }

    /// A higher order term is one that has a variable as its head.
    pub fn is_higher_order(&self) -> bool {
        matches!(self.get_head_atom(), Atom::Variable(_))
    }

    /// Recursively checks if any term has a variable as its head with arguments applied to it.
    /// Returns true for terms like x0(a, b) but false for plain variables like x0.
    pub fn has_any_applied_variable(&self) -> bool {
        // Check if this term itself is an applied variable
        if matches!(self.get_head_atom(), Atom::Variable(_)) && self.num_args() > 0 {
            return true;
        }
        // Recursively check arguments
        for arg in self.iter_args() {
            if arg.has_any_applied_variable() {
                return true;
            }
        }
        false
    }

    /// Count the number of atom components (excluding Composite markers).
    pub fn atom_count(&self) -> u32 {
        let mut count = 0;
        for component in self.components {
            if let ThinTermComponent::Atom(Atom::True) = component {
                continue; // "true" counts as 0
            }
            if matches!(component, ThinTermComponent::Atom(_)) {
                count += 1;
            }
        }
        count
    }

    /// Get the number of arguments this term has.
    pub fn num_args(&self) -> usize {
        if self.components.len() <= 1 {
            return 0;
        }

        let mut arg_count = 0;
        let mut i = 1; // Skip the head
        while i < self.components.len() {
            arg_count += 1;
            if let ThinTermComponent::Composite { span } = self.components[i] {
                i += span as usize;
            } else {
                i += 1;
            }
        }
        arg_count
    }

    /// Iterate over the arguments of this term without allocating.
    /// Each argument is returned as a ThinTermRef.
    pub fn iter_args(&self) -> ThinTermRefArgsIterator<'a> {
        ThinTermRefArgsIterator {
            components: self.components,
            position: if self.components.len() > 1 {
                1
            } else {
                self.components.len()
            },
        }
    }

    /// Iterate over all atoms in the term.
    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom> + 'a {
        self.components.iter().filter_map(|component| {
            if let ThinTermComponent::Atom(atom) = component {
                Some(atom)
            } else {
                None
            }
        })
    }

    /// Get the maximum variable index in this term, or None if there are no variables.
    pub fn max_variable(&self) -> Option<AtomId> {
        let mut max: Option<AtomId> = None;
        for atom in self.iter_atoms() {
            if let Atom::Variable(i) = atom {
                max = Some(match max {
                    None => *i,
                    Some(current_max) => current_max.max(*i),
                });
            }
        }
        max
    }

    /// Get the lowest variable number this term doesn't use.
    pub fn least_unused_variable(&self) -> AtomId {
        match self.max_variable() {
            Some(max) => max + 1,
            None => 0,
        }
    }

    /// Calculate multi-weight for KBO ordering.
    /// Returns (weight1, weight2) and populates refcounts with variable usage.
    fn multi_weight(&self, refcounts: &mut Vec<u8>) -> (u32, u32) {
        use crate::kernel::symbol::Symbol;

        let mut weight1 = 0;
        let mut weight2 = 0;

        for component in self.components {
            match component {
                ThinTermComponent::Composite { .. } => {
                    // Composite markers don't contribute to weight
                }
                ThinTermComponent::Atom(Atom::True) => {
                    // True doesn't contribute to weight
                }
                ThinTermComponent::Atom(Atom::Variable(i)) => {
                    while refcounts.len() <= *i as usize {
                        refcounts.push(0);
                    }
                    refcounts[*i as usize] += 1;
                }
                ThinTermComponent::Atom(Atom::Symbol(Symbol::GlobalConstant(i))) => {
                    weight1 += 1;
                    weight2 += 4 * (*i) as u32;
                }
                ThinTermComponent::Atom(Atom::Symbol(Symbol::ScopedConstant(i))) => {
                    weight1 += 1;
                    weight2 += 1 + 4 * (*i) as u32;
                }
                ThinTermComponent::Atom(Atom::Symbol(Symbol::Monomorph(i))) => {
                    weight1 += 1;
                    weight2 += 2 + 4 * (*i) as u32;
                }
                ThinTermComponent::Atom(Atom::Symbol(Symbol::Synthetic(i))) => {
                    weight1 += 1;
                    weight2 += 3 + 4 * (*i) as u32;
                }
            }
        }

        (weight1, weight2)
    }

    /// KBO helper that can skip the domination check.
    fn kbo_helper(&self, other: &ThinTermRef, check_domination: bool) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let mut self_refcounts = vec![];
        let (self_weight1, self_weight2) = self.multi_weight(&mut self_refcounts);

        let mut other_refcounts = vec![];
        let (other_weight1, other_weight2) = other.multi_weight(&mut other_refcounts);

        if self_weight1 > other_weight1
            || self_weight1 == other_weight1 && self_weight2 > other_weight2
        {
            if !check_domination || dominates(&self_refcounts, &other_refcounts) {
                return Ordering::Greater;
            }
            return Ordering::Equal;
        }

        if self_weight1 < other_weight1
            || self_weight1 == other_weight1 && self_weight2 < other_weight2
        {
            if !check_domination || dominates(&other_refcounts, &self_refcounts) {
                return Ordering::Less;
            }
            return Ordering::Equal;
        }

        Ordering::Equal
    }

    /// Partial tiebreak for KBO - stable under variable renaming.
    fn partial_tiebreak(&self, other: &ThinTermRef) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let head_cmp = self
            .get_head_atom()
            .stable_partial_order(other.get_head_atom());
        if head_cmp != Ordering::Equal {
            return head_cmp;
        }

        // More arguments means simpler (less nested)
        let len_cmp = other.num_args().cmp(&self.num_args());
        if len_cmp != Ordering::Equal {
            return len_cmp;
        }

        // Compare arguments lexicographically
        for (arg1, arg2) in self.iter_args().zip(other.iter_args()) {
            let arg_cmp = arg1.partial_tiebreak(&arg2);
            if arg_cmp != Ordering::Equal {
                return arg_cmp;
            }
        }

        Ordering::Equal
    }

    /// Total tiebreak for KBO - not stable under variable renaming.
    fn total_tiebreak(&self, other: &ThinTermRef) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let head_cmp = other.get_head_atom().cmp(self.get_head_atom());
        if head_cmp != Ordering::Equal {
            return head_cmp;
        }

        // The partial tiebreak should have caught this
        debug_assert!(self.num_args() == other.num_args());

        // Compare arguments lexicographically
        for (arg1, arg2) in self.iter_args().zip(other.iter_args()) {
            let arg_cmp = arg1.extended_kbo_cmp(&arg2);
            if arg_cmp != Ordering::Equal {
                return arg_cmp;
            }
        }

        Ordering::Equal
    }

    /// Knuth-Bendix partial reduction ordering.
    /// Returns Greater if self > other, Less if other > self.
    /// Returns Equal if they cannot be ordered (not equality in the usual sense).
    pub fn kbo_cmp(&self, other: &ThinTermRef) -> std::cmp::Ordering {
        self.kbo_helper(other, true)
    }

    /// Extended KBO comparison - total ordering where only identical terms are equal.
    pub fn extended_kbo_cmp(&self, other: &ThinTermRef) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let kbo_cmp = self.kbo_helper(other, false);
        if kbo_cmp != Ordering::Equal {
            return kbo_cmp;
        }

        let tiebreak = self.partial_tiebreak(other);
        if tiebreak != Ordering::Equal {
            return tiebreak;
        }

        self.total_tiebreak(other)
    }
}

impl fmt::Display for ThinTermRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Format the term by walking through components
        format_term_at(f, self.components, 0)
    }
}

/// Helper function to format a term starting at the given position.
/// Returns the position after the formatted term.
fn format_term_at(
    f: &mut fmt::Formatter,
    components: &[ThinTermComponent],
    pos: usize,
) -> fmt::Result {
    if pos >= components.len() {
        return Ok(());
    }

    match &components[pos] {
        ThinTermComponent::Composite { span } => {
            // This shouldn't happen at the start of a term, but handle it
            // by formatting the contents (skip the Composite marker)
            let end = pos + *span as usize;
            format_composite_contents(f, components, pos + 1, end)
        }
        ThinTermComponent::Atom(atom) => {
            // Format the head atom
            match atom {
                Atom::Variable(i) => write!(f, "x{}", i)?,
                _ => write!(f, "{}", atom)?,
            }
            // Check if there are arguments following
            if pos + 1 < components.len() {
                // Format the arguments
                write!(f, "(")?;
                let mut arg_pos = pos + 1;
                let mut first = true;
                while arg_pos < components.len() {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    arg_pos = format_arg_at(f, components, arg_pos)?;
                }
                write!(f, ")")?;
            }
            Ok(())
        }
    }
}

/// Format an argument at the given position.
/// Returns the position after the argument.
fn format_arg_at(
    f: &mut fmt::Formatter,
    components: &[ThinTermComponent],
    pos: usize,
) -> Result<usize, fmt::Error> {
    match &components[pos] {
        ThinTermComponent::Composite { span } => {
            // Format the composite subterm
            let end = pos + *span as usize;
            format_composite_contents(f, components, pos + 1, end)?;
            Ok(end)
        }
        ThinTermComponent::Atom(atom) => {
            // Simple atom argument
            match atom {
                Atom::Variable(i) => write!(f, "x{}", i)?,
                _ => write!(f, "{}", atom)?,
            }
            Ok(pos + 1)
        }
    }
}

/// Format the contents of a composite (head + args) from start to end.
fn format_composite_contents(
    f: &mut fmt::Formatter,
    components: &[ThinTermComponent],
    start: usize,
    end: usize,
) -> fmt::Result {
    if start >= end {
        return Ok(());
    }

    // The first element after Composite marker is the head
    match &components[start] {
        ThinTermComponent::Atom(atom) => match atom {
            Atom::Variable(i) => write!(f, "x{}", i)?,
            _ => write!(f, "{}", atom)?,
        },
        ThinTermComponent::Composite { .. } => {
            // Nested composite as head - shouldn't normally happen
            return Err(fmt::Error);
        }
    }

    // Format arguments if any
    if start + 1 < end {
        write!(f, "(")?;
        let mut arg_pos = start + 1;
        let mut first = true;
        while arg_pos < end {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            arg_pos = format_arg_at(f, components, arg_pos)?;
        }
        write!(f, ")")?;
    }

    Ok(())
}

/// A thin term stores term structure without type information.
/// Type information is stored separately in the TypeStore and SymbolTable.
/// The term is represented as a flat vector of components in pre-order traversal.
/// The first element is always the head atom, followed by the arguments.
///
/// Examples:
/// - Simple atom "a": [Atom(a)]
/// - Application "f(a)": [Atom(f), Atom(a)]
/// - Nested "f(a, g(b))": [Atom(f), Atom(a), Composite{span: 3}, Atom(g), Atom(b)]
///                                            ^--- this composite has span 3: the marker, g, and b
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct ThinTerm {
    components: Vec<ThinTermComponent>,
}

impl ThinTerm {
    /// Create a new ThinTerm with the same signature as FatTerm::new.
    /// The term_type and head_type parameters are ignored since ThinTerm stores types externally.
    pub fn new(
        _term_type: TypeId,
        _head_type: TypeId,
        head: Atom,
        args: Vec<ThinTerm>,
    ) -> ThinTerm {
        let mut components = vec![ThinTermComponent::Atom(head)];
        for arg in args {
            if arg.components.len() == 1 {
                // Atomic argument - just add the atom
                components.push(arg.components[0]);
            } else {
                // Compound argument - add Composite marker with span
                components.push(ThinTermComponent::Composite {
                    span: arg.components.len() as u16 + 1,
                });
                components.extend(arg.components.iter().copied());
            }
        }
        ThinTerm { components }
    }

    /// Create a new ThinTerm from a vector of components.
    pub fn from_components(components: Vec<ThinTermComponent>) -> ThinTerm {
        ThinTerm { components }
    }

    /// Create a ThinTerm representing a single atom with no arguments.
    /// The type_id parameter is accepted for API compatibility with FatTerm but is ignored
    /// since ThinTerm stores types separately.
    pub fn atom(_type_id: TypeId, atom: Atom) -> ThinTerm {
        ThinTerm {
            components: vec![ThinTermComponent::Atom(atom)],
        }
    }

    /// Parse a ThinTerm from a string representation.
    /// Format: "f(a, g(b))" or just "x0" for atoms.
    /// Variables are written as x0, x1, etc.
    /// Constants are written as c0, c1, etc.
    pub fn parse(s: &str) -> ThinTerm {
        let s = s.trim();

        if s == "true" {
            return ThinTerm::atom(BOOL, Atom::True);
        }

        let first_paren = match s.find('(') {
            Some(i) => i,
            None => return ThinTerm::atom(EMPTY, Atom::new(s)),
        };

        // Figure out which commas are inside precisely one level of parentheses.
        let mut terminator_indices = vec![];
        let mut num_parens = 0;
        for (i, c) in s.chars().enumerate() {
            match c {
                '(' => num_parens += 1,
                ')' => {
                    num_parens -= 1;
                    if num_parens == 0 {
                        terminator_indices.push(i);
                    }
                }
                ',' => {
                    if num_parens == 1 {
                        terminator_indices.push(i);
                    }
                }
                _ => (),
            }
        }

        // Split the string into the head and the args.
        let head = &s[0..first_paren];
        let mut args = vec![];
        for (i, terminator_index) in terminator_indices.iter().enumerate() {
            let start = if i == 0 {
                first_paren + 1
            } else {
                terminator_indices[i - 1] + 1
            };
            args.push(ThinTerm::parse(&s[start..*terminator_index]));
        }

        // Build the component vector
        let mut components = vec![ThinTermComponent::Atom(Atom::new(head))];
        for arg in args {
            if arg.components.len() == 1 {
                // Atomic argument - just add the atom
                components.push(arg.components[0]);
            } else {
                // Compound argument - add Composite marker with span
                components.push(ThinTermComponent::Composite {
                    span: arg.components.len() as u16 + 1,
                });
                components.extend(arg.components);
            }
        }

        ThinTerm { components }
    }

    /// Get the components of this thin term.
    pub fn components(&self) -> &[ThinTermComponent] {
        &self.components
    }

    /// Get a borrowed reference to this term.
    pub fn as_ref(&self) -> ThinTermRef {
        ThinTermRef::new(&self.components)
    }

    /// Get the head atom of this term.
    pub fn get_head_atom(&self) -> &Atom {
        match &self.components[0] {
            ThinTermComponent::Atom(atom) => atom,
            ThinTermComponent::Composite { .. } => {
                panic!("ThinTerm should not start with Composite marker")
            }
        }
    }

    /// Get the term type with context.
    /// Uses LocalContext for variable types and KernelContext for symbol types.
    /// For function applications, applies the function type once per argument.
    pub fn get_term_type_with_context(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> TypeId {
        // Start with the head type
        let mut result_type = self.get_head_type_with_context(local_context, kernel_context);

        // Apply the type once per argument
        for _ in self.iter_args() {
            result_type = kernel_context
                .type_store
                .apply_type(result_type)
                .expect("Function type expected but not found during type application");
        }

        result_type
    }

    /// Get the head type with context.
    /// Uses LocalContext for variable types and KernelContext for symbol types.
    pub fn get_head_type_with_context(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> TypeId {
        let head = self.get_head_atom();
        match head {
            Atom::Variable(i) => local_context
                .get_var_type(*i as usize)
                .expect("Variable not found in LocalContext"),
            Atom::Symbol(symbol) => kernel_context.symbol_table.get_type(*symbol),
            Atom::True => BOOL,
        }
    }

    /// Check if this term is atomic (no arguments).
    pub fn is_atomic(&self) -> bool {
        self.as_ref().is_atomic()
    }

    /// Check if this term is the boolean constant "true".
    pub fn is_true(&self) -> bool {
        self.as_ref().is_true()
    }

    /// Create a new ThinTerm representing the boolean constant "true".
    pub fn new_true() -> ThinTerm {
        ThinTerm::atom(BOOL, Atom::True)
    }

    /// Create a new ThinTerm representing a variable with the given index.
    /// The type_id parameter is accepted for API compatibility with FatTerm but is ignored
    /// since ThinTerm stores types separately in the context.
    pub fn new_variable(_type_id: TypeId, index: AtomId) -> ThinTerm {
        ThinTerm {
            components: vec![ThinTermComponent::Atom(Atom::Variable(index))],
        }
    }

    /// A higher order term is one that has a variable as its head.
    pub fn is_higher_order(&self) -> bool {
        matches!(self.get_head_atom(), Atom::Variable(_))
    }

    /// Recursively checks if any term has a variable as its head with arguments applied to it.
    /// Returns true for terms like x0(a, b) but false for plain variables like x0.
    pub fn has_any_applied_variable(&self) -> bool {
        // Check if this term itself is an applied variable
        if matches!(self.get_head_atom(), Atom::Variable(_)) && self.num_args() > 0 {
            return true;
        }
        // Recursively check arguments
        for arg in self.iter_args() {
            if arg.has_any_applied_variable() {
                return true;
            }
        }
        false
    }

    /// Check if this term is a variable (atomic and head is a variable).
    pub fn is_variable(&self) -> bool {
        self.as_ref().is_variable()
    }

    /// If this is an atomic variable, return its index.
    pub fn atomic_variable(&self) -> Option<AtomId> {
        self.as_ref().atomic_variable()
    }

    /// Check if this term contains a variable with the given index anywhere.
    pub fn has_variable(&self, index: AtomId) -> bool {
        self.as_ref().has_variable(index)
    }

    /// Check if this term contains any variables.
    pub fn has_any_variable(&self) -> bool {
        self.as_ref().has_any_variable()
    }

    /// Check if this term contains any local constants.
    pub fn has_scoped_constant(&self) -> bool {
        self.as_ref().has_scoped_constant()
    }

    /// Check if this term contains any synthetic atoms.
    pub fn has_synthetic(&self) -> bool {
        self.as_ref().has_synthetic()
    }

    /// Count the number of atom components (excluding Composite markers).
    pub fn atom_count(&self) -> u32 {
        self.as_ref().atom_count()
    }

    /// Get the number of arguments this term has.
    pub fn num_args(&self) -> usize {
        self.as_ref().num_args()
    }

    /// Iterate over the arguments of this term without allocating.
    /// Each argument is returned as a ThinTermRef.
    pub fn iter_args(&self) -> ThinTermRefArgsIterator {
        self.as_ref().iter_args()
    }

    /// Get the arguments of this term as owned ThinTerms.
    /// This allocates a new vector, unlike iter_args() which borrows.
    pub fn args(&self) -> Vec<ThinTerm> {
        self.iter_args().map(|arg| arg.to_owned()).collect()
    }

    /// Get a specific argument by index.
    pub fn get_arg(&self, index: usize) -> Option<ThinTerm> {
        self.iter_args().nth(index).map(|arg| arg.to_owned())
    }

    /// Iterate over all atoms in the term.
    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom> + '_ {
        self.components.iter().filter_map(|component| {
            if let ThinTermComponent::Atom(atom) = component {
                Some(atom)
            } else {
                None
            }
        })
    }

    /// Returns the head of this term as a ThinTerm with no arguments.
    pub fn get_head_term(&self) -> ThinTerm {
        ThinTerm {
            components: vec![ThinTermComponent::Atom(*self.get_head_atom())],
        }
    }

    /// Collects all variables in the term (recursively through arguments).
    /// Returns (AtomId, TypeId) pairs for each variable found.
    /// Uses the local_context to look up variable types.
    pub fn collect_vars(&self, local_context: &LocalContext) -> Vec<(AtomId, TypeId)> {
        let mut result = Vec::new();
        for atom in self.iter_atoms() {
            if let Atom::Variable(id) = atom {
                let type_id = local_context
                    .get_var_type(*id as usize)
                    .expect("Variable not found in local context");
                result.push((*id, type_id));
            }
        }
        result
    }

    /// Get the type of a variable if it appears in this term.
    pub fn var_type(&self, index: AtomId, local_context: &LocalContext) -> Option<TypeId> {
        if self.has_variable(index) {
            local_context.get_var_type(index as usize)
        } else {
            None
        }
    }

    /// Returns all (TypeId, Atom) pairs in this term.
    /// Does not deduplicate.
    pub fn typed_atoms(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<(TypeId, Atom)> {
        let mut result = Vec::new();
        for atom in self.iter_atoms() {
            let type_id = match atom {
                Atom::Variable(id) => local_context
                    .get_var_type(*id as usize)
                    .expect("Variable not found in local context"),
                Atom::Symbol(symbol) => kernel_context.symbol_table.get_type(*symbol),
                Atom::True => BOOL,
            };
            result.push((type_id, *atom));
        }
        result
    }

    /// Get the maximum variable index in this term, or None if there are no variables.
    pub fn max_variable(&self) -> Option<AtomId> {
        self.as_ref().max_variable()
    }

    /// Get the lowest variable number this term doesn't use.
    pub fn least_unused_variable(&self) -> AtomId {
        self.as_ref().least_unused_variable()
    }

    /// Replace all occurrences of a variable with a term.
    /// This handles the complexity of updating Composite span markers when
    /// the replacement term has a different size than the variable (1 component).
    pub fn replace_variable(&self, id: AtomId, value: &ThinTerm) -> ThinTerm {
        // Build the result by processing components, tracking size changes for spans
        let mut result = Vec::new();
        self.replace_variable_recursive(&mut result, id, value);
        ThinTerm::from_components(result)
    }

    /// Helper for replace_variable that processes components recursively.
    /// Returns the number of components added to result.
    fn replace_variable_recursive(
        &self,
        result: &mut Vec<ThinTermComponent>,
        id: AtomId,
        value: &ThinTerm,
    ) -> usize {
        let mut i = 0;
        let mut added = 0;

        while i < self.components.len() {
            match &self.components[i] {
                ThinTermComponent::Atom(Atom::Variable(var_id)) if *var_id == id => {
                    // Replace this variable with the value's components
                    if value.components.len() == 1 {
                        // Simple replacement - just copy the single component
                        result.push(value.components[0]);
                        added += 1;
                    } else {
                        // Complex replacement - need to wrap in Composite
                        result.push(ThinTermComponent::Composite {
                            span: value.components.len() as u16 + 1,
                        });
                        result.extend(value.components.iter().copied());
                        added += value.components.len() + 1;
                    }
                    i += 1;
                }
                ThinTermComponent::Atom(atom) => {
                    // Non-matching atom - copy as-is
                    result.push(ThinTermComponent::Atom(*atom));
                    added += 1;
                    i += 1;
                }
                ThinTermComponent::Composite { span } => {
                    // Process the composite subterm recursively
                    let subterm_start = i + 1;
                    let subterm_end = i + *span as usize;

                    // Create a temporary ThinTerm for the subterm (excluding Composite marker)
                    let subterm = ThinTerm::from_components(
                        self.components[subterm_start..subterm_end].to_vec(),
                    );

                    // Recursively replace in the subterm
                    let mut sub_result = Vec::new();
                    subterm.replace_variable_recursive(&mut sub_result, id, value);

                    // If the subterm is now atomic (single component), don't wrap it
                    if sub_result.len() == 1 {
                        result.push(sub_result[0]);
                        added += 1;
                    } else {
                        // Add a new Composite marker with the correct span
                        result.push(ThinTermComponent::Composite {
                            span: sub_result.len() as u16 + 1,
                        });
                        result.extend(sub_result.iter().copied());
                        added += sub_result.len() + 1;
                    }

                    i = subterm_end;
                }
            }
        }

        added
    }

    /// Replace multiple variables at once.
    pub fn replace_variables(
        &self,
        var_ids: &[AtomId],
        replacement_terms: &[&ThinTerm],
    ) -> ThinTerm {
        if var_ids.is_empty() {
            return self.clone();
        }

        // Apply replacements one at a time
        // This could be optimized to do all at once, but this is simpler
        let mut result = self.clone();
        for (id, term) in var_ids.iter().zip(replacement_terms.iter()) {
            result = result.replace_variable(*id, term);
        }
        result
    }

    /// Replace an atom with another atom throughout the term.
    pub fn replace_atom(&self, old_atom: &Atom, new_atom: &Atom) -> ThinTerm {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                ThinTermComponent::Atom(atom) if atom == old_atom => {
                    ThinTermComponent::Atom(*new_atom)
                }
                c => *c,
            })
            .collect();
        ThinTerm::from_components(new_components)
    }

    /// Renumbers synthetic atoms from the provided list into the invalid range.
    pub fn invalidate_synthetics(&self, from: &[AtomId]) -> ThinTerm {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                ThinTermComponent::Atom(atom) => {
                    ThinTermComponent::Atom(atom.invalidate_synthetics(from))
                }
                c => *c,
            })
            .collect();
        ThinTerm::from_components(new_components)
    }

    /// Replace the first `num_to_replace` variables with invalid synthetic atoms, adjusting
    /// the subsequent variable ids accordingly.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> ThinTerm {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                ThinTermComponent::Atom(atom) => {
                    ThinTermComponent::Atom(atom.instantiate_invalid_synthetics(num_to_replace))
                }
                c => *c,
            })
            .collect();
        ThinTerm::from_components(new_components)
    }

    /// Normalize variable IDs in place, tracking types from the input context.
    /// This is used when reversing literals to build a new context.
    pub fn normalize_var_ids_with_types(
        &mut self,
        var_ids: &mut Vec<AtomId>,
        var_types: &mut Vec<TypeId>,
        input_context: &LocalContext,
    ) {
        for component in &mut self.components {
            if let ThinTermComponent::Atom(Atom::Variable(i)) = component {
                let pos = var_ids.iter().position(|&x| x == *i);
                match pos {
                    Some(j) => *i = j as AtomId,
                    None => {
                        let new_id = var_ids.len() as AtomId;
                        var_ids.push(*i);
                        // Look up the type from the input context using the original variable ID
                        let var_type = input_context
                            .get_var_type(*i as usize)
                            .expect("Variable not found in input context during renumbering");
                        var_types.push(var_type);
                        *i = new_id;
                    }
                }
            }
        }
    }

    /// Find atoms whose term (not just head) has a specific type.
    /// Returns the head atom of each subterm that has the matching type.
    pub fn atoms_for_type(
        &self,
        type_id: TypeId,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<Atom> {
        let mut result = Vec::new();

        // Check if this term's type matches
        let my_type = self.get_term_type_with_context(local_context, kernel_context);
        if my_type == type_id {
            result.push(*self.get_head_atom());
        }

        // Recursively check arguments
        for arg in self.iter_args() {
            let arg_owned = arg.to_owned();
            result.append(&mut arg_owned.atoms_for_type(type_id, local_context, kernel_context));
        }

        result
    }

    /// Remap variables according to a mapping.
    /// Replaces x_i with x_{var_map[i]}.
    pub fn remap_variables(&self, var_map: &[AtomId]) -> ThinTerm {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                ThinTermComponent::Atom(atom) => {
                    ThinTermComponent::Atom(atom.remap_variables(var_map))
                }
                c => *c,
            })
            .collect();
        ThinTerm::from_components(new_components)
    }

    /// Build a term from a spine (function + arguments).
    /// If the spine has one element, returns just that element.
    /// Otherwise, treats the first element as the function and the rest as arguments.
    pub fn from_spine(mut spine: Vec<ThinTerm>) -> ThinTerm {
        if spine.is_empty() {
            panic!("from_spine called with empty spine");
        }

        if spine.len() == 1 {
            // Just the function, no arguments
            spine.pop().unwrap()
        } else {
            // Take the function (first element)
            let func = spine.remove(0);
            let func_args = func.args();

            // Combine the function's existing args with the new ones
            let mut all_args = func_args;
            all_args.extend(spine);

            // Build the new term
            let mut components = vec![ThinTermComponent::Atom(*func.get_head_atom())];
            for arg in all_args {
                if arg.components.len() == 1 {
                    components.push(arg.components[0]);
                } else {
                    components.push(ThinTermComponent::Composite {
                        span: arg.components.len() as u16 + 1,
                    });
                    components.extend(arg.components.iter().copied());
                }
            }
            ThinTerm::from_components(components)
        }
    }

    /// Apply additional arguments to this term.
    pub fn apply(&self, args: &[ThinTerm]) -> ThinTerm {
        if args.is_empty() {
            return self.clone();
        }

        let mut components = self.components.clone();
        for arg in args {
            if arg.components.len() == 1 {
                components.push(arg.components[0]);
            } else {
                components.push(ThinTermComponent::Composite {
                    span: arg.components.len() as u16 + 1,
                });
                components.extend(arg.components.iter().copied());
            }
        }
        ThinTerm::from_components(components)
    }

    /// Replace all arguments with new arguments.
    pub fn replace_args(&self, new_args: Vec<ThinTerm>) -> ThinTerm {
        let mut components = vec![ThinTermComponent::Atom(*self.get_head_atom())];
        for arg in new_args {
            if arg.components.len() == 1 {
                components.push(arg.components[0]);
            } else {
                components.push(ThinTermComponent::Composite {
                    span: arg.components.len() as u16 + 1,
                });
                components.extend(arg.components.iter().copied());
            }
        }
        ThinTerm::from_components(components)
    }

    /// Knuth-Bendix partial reduction ordering.
    /// Returns Greater if self > other, Less if other > self.
    /// Returns Equal if they cannot be ordered (not equality in the usual sense).
    pub fn kbo_cmp(&self, other: &ThinTerm) -> std::cmp::Ordering {
        self.as_ref().kbo_cmp(&other.as_ref())
    }

    /// Extended KBO comparison - total ordering where only identical terms are equal.
    pub fn extended_kbo_cmp(&self, other: &ThinTerm) -> std::cmp::Ordering {
        self.as_ref().extended_kbo_cmp(&other.as_ref())
    }

    /// Normalize variable IDs in place so they appear in order of first occurrence.
    /// The var_ids vector tracks which original variable IDs have been seen.
    /// This mutates the term in place.
    pub fn normalize_var_ids(&mut self, var_ids: &mut Vec<AtomId>) {
        for component in &mut self.components {
            if let ThinTermComponent::Atom(Atom::Variable(i)) = component {
                let pos = var_ids.iter().position(|&x| x == *i);
                match pos {
                    Some(j) => *i = j as AtomId,
                    None => {
                        let new_id = var_ids.len() as AtomId;
                        var_ids.push(*i);
                        *i = new_id;
                    }
                }
            }
        }
    }

    /// Get the subterm at the given path.
    /// A path is a sequence of argument indices to follow.
    /// An empty path returns the whole term.
    pub fn get_term_at_path(&self, path: &[usize]) -> Option<ThinTerm> {
        if path.is_empty() {
            return Some(self.clone());
        }

        // Navigate to the argument at path[0]
        let arg_index = path[0];
        let mut current_pos = 1; // Skip the head
        let mut current_arg = 0;

        while current_pos < self.components.len() && current_arg < arg_index {
            // Skip this argument
            match self.components[current_pos] {
                ThinTermComponent::Composite { span } => {
                    current_pos += span as usize;
                }
                ThinTermComponent::Atom(_) => {
                    current_pos += 1;
                }
            }
            current_arg += 1;
        }

        if current_arg != arg_index || current_pos >= self.components.len() {
            return None;
        }

        // Extract the argument at current_pos
        let arg = match self.components[current_pos] {
            ThinTermComponent::Composite { span } => {
                // The argument spans from current_pos to current_pos + span
                // But the Composite marker isn't part of the term's components, so skip it
                ThinTerm::from_components(
                    self.components[current_pos + 1..current_pos + span as usize].to_vec(),
                )
            }
            ThinTermComponent::Atom(atom) => {
                ThinTerm::from_components(vec![ThinTermComponent::Atom(atom)])
            }
        };

        // Recurse for the rest of the path
        arg.get_term_at_path(&path[1..])
    }

    /// Replace the subterm at the given path with a replacement.
    /// A path is a sequence of argument indices to follow.
    /// An empty path replaces the whole term.
    pub fn replace_at_path(&self, path: &[usize], replacement: ThinTerm) -> ThinTerm {
        if path.is_empty() {
            return replacement;
        }

        // We need to rebuild the term with the replacement at the path
        let mut new_components = vec![self.components[0]]; // Keep the head

        let arg_index = path[0];
        let mut current_pos = 1; // Skip the head
        let mut current_arg = 0;

        while current_pos < self.components.len() {
            let arg_start = current_pos;
            let arg_end = match self.components[current_pos] {
                ThinTermComponent::Composite { span } => current_pos + span as usize,
                ThinTermComponent::Atom(_) => current_pos + 1,
            };

            if current_arg == arg_index {
                // This is the argument to replace (or recurse into)
                let old_arg = match self.components[arg_start] {
                    ThinTermComponent::Composite { span } => ThinTerm::from_components(
                        self.components[arg_start + 1..arg_start + span as usize].to_vec(),
                    ),
                    ThinTermComponent::Atom(atom) => {
                        ThinTerm::from_components(vec![ThinTermComponent::Atom(atom)])
                    }
                };

                let new_arg = old_arg.replace_at_path(&path[1..], replacement.clone());

                // Add the new argument to components
                if new_arg.components.len() == 1 {
                    new_components.push(new_arg.components[0]);
                } else {
                    new_components.push(ThinTermComponent::Composite {
                        span: new_arg.components.len() as u16 + 1,
                    });
                    new_components.extend(new_arg.components.iter().copied());
                }
            } else {
                // Copy this argument unchanged
                new_components.extend(self.components[arg_start..arg_end].iter().copied());
            }

            current_pos = arg_end;
            current_arg += 1;
        }

        ThinTerm::from_components(new_components)
    }

    /// Find all rewritable subterms with their paths.
    /// It is an error to call this on any variables.
    /// Any term is rewritable except for "true".
    pub fn rewritable_subterms(&self) -> Vec<(Vec<usize>, ThinTerm)> {
        let mut answer = vec![];
        let mut prefix = vec![];
        self.push_rewritable_subterms(&mut prefix, &mut answer);
        answer
    }

    /// Helper for rewritable_subterms.
    fn push_rewritable_subterms(
        &self,
        prefix: &mut Vec<usize>,
        answer: &mut Vec<(Vec<usize>, ThinTerm)>,
    ) {
        if self.is_true() {
            return;
        }
        if self.is_variable() {
            panic!("expected no variables");
        }

        // Process arguments first (prefix order)
        for (i, arg) in self.iter_args().enumerate() {
            prefix.push(i);
            arg.to_owned().push_rewritable_subterms(prefix, answer);
            prefix.pop();
        }

        // Add this term itself
        answer.push((prefix.clone(), self.clone()));
    }
}

impl fmt::Display for ThinTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

/// Helper function for KBO domination check.
fn dominates(a: &Vec<u8>, b: &Vec<u8>) -> bool {
    if b.len() > a.len() {
        return false;
    }
    for i in 0..b.len() {
        if a[i] < b[i] {
            return false;
        }
    }
    true
}

/// Iterator over the arguments of a ThinTermRef, yielding borrowed references.
pub struct ThinTermRefArgsIterator<'a> {
    components: &'a [ThinTermComponent],
    position: usize,
}

impl<'a> Iterator for ThinTermRefArgsIterator<'a> {
    type Item = ThinTermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position >= self.components.len() {
            return None;
        }

        match self.components[self.position] {
            ThinTermComponent::Composite { span } => {
                // Extract the composite term as a slice reference
                let arg_slice = &self.components[self.position..self.position + span as usize];
                self.position += span as usize;
                Some(ThinTermRef::new(arg_slice))
            }
            ThinTermComponent::Atom(_) => {
                // Simple atomic argument as a single-element slice
                let arg_slice = &self.components[self.position..self.position + 1];
                self.position += 1;
                Some(ThinTermRef::new(arg_slice))
            }
        }
    }
}
