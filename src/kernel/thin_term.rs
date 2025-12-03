use serde::{Deserialize, Serialize};
use std::fmt;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::fat_term::{TypeId, BOOL, EMPTY};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol_table::SymbolTable;
use crate::kernel::type_store::TypeStore;

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
    /// Create a new ThinTerm from a vector of components.
    pub fn new(components: Vec<ThinTermComponent>) -> ThinTerm {
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

    /// Get the type of this term.
    /// Requires context to look up the type information.
    pub fn get_term_type(
        &self,
        _context: &LocalContext,
        symbol_table: &SymbolTable,
        _type_store: &TypeStore,
    ) -> TypeId {
        // For a simple atom with no arguments, the term type equals the head type
        if self.is_atomic() {
            return self.get_head_type(symbol_table);
        }

        // For function applications, we need to compute the result type
        // This is a placeholder - full implementation needs type inference
        todo!("get_term_type for non-atomic terms requires type inference")
    }

    /// Get the term type with context (for API compatibility with FatTerm).
    /// Uses LocalContext for variable types and KernelContext for symbol types.
    pub fn get_term_type_with_context(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> TypeId {
        // For a simple atom with no arguments, the term type equals the head type
        if self.is_atomic() {
            return self.get_head_type_with_context(local_context, kernel_context);
        }

        // For function applications, we need to compute the result type
        // This is a placeholder - full implementation needs type inference
        todo!("get_term_type_with_context for non-atomic terms requires type inference")
    }

    /// Get the type of the head atom (non-variable version).
    ///
    /// WARNING: This panics if the head is a variable. For variables, use get_head_type_with_context instead.
    pub fn get_head_type(&self, symbol_table: &SymbolTable) -> TypeId {
        let head = self.get_head_atom();
        match head {
            Atom::Variable(_) => {
                panic!("ThinTerm::get_head_type called on variable - use get_head_type_with_context instead")
            }
            Atom::Symbol(symbol) => symbol_table.get_type(*symbol),
            Atom::True => crate::kernel::fat_term::BOOL,
        }
    }

    /// Get the head type with context (for API compatibility with FatTerm).
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

    /// Get the maximum variable index in this term, or None if there are no variables.
    pub fn max_variable(&self) -> Option<AtomId> {
        self.as_ref().max_variable()
    }

    /// Get the lowest variable number this term doesn't use.
    pub fn least_unused_variable(&self) -> AtomId {
        self.as_ref().least_unused_variable()
    }

    /// Replace all occurrences of a variable with a term.
    ///
    /// WARNING: Current implementation is INCORRECT!
    /// When replacing variables, we need to:
    /// 1. Recursively process subterms (respecting Composite span markers)
    /// 2. Update span markers when the replacement changes the size
    /// 3. Handle the case where a variable is replaced with a complex term
    ///
    /// TODO: Implement proper recursive replacement with span adjustment.
    /// This is complex because we need to:
    /// - Track the size change when replacing a variable (1 component) with value (N components)
    /// - Update all parent Composite markers to reflect the new spans
    /// - Process subterms recursively
    pub fn replace_variable(&self, _id: AtomId, _value: &ThinTerm) -> ThinTerm {
        todo!(
            "ThinTerm::replace_variable needs proper implementation with span adjustment. \
             Current naive implementation breaks span invariants when replacing variables with complex terms."
        )
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
        ThinTerm::new(new_components)
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
        ThinTerm::new(new_components)
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
