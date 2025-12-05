use serde::{Deserialize, Serialize};
use std::fmt;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::types::{TypeId, BOOL, EMPTY};

/// A component of a Term in its flattened representation.
/// Either a Composite node or an Atom leaf node.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum TermComponent {
    /// Indicates a composite argument with the given span (total number of components).
    /// The span includes this Composite marker itself, the head, and all arguments recursively.
    /// To skip over this entire subterm: index += span
    /// To enter this subterm (process the head): index += 1
    Composite { span: u16 },

    /// A leaf atom in the term tree.
    Atom(Atom),
}

/// A borrowed reference to a term - wraps a slice of components.
/// This is the borrowed equivalent of Term, similar to how &str relates to String.
/// Most operations work on TermRef to avoid unnecessary allocations.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct TermRef<'a> {
    components: &'a [TermComponent],
}

impl<'a> TermRef<'a> {
    /// Create a TermRef from a slice of components.
    pub fn new(components: &'a [TermComponent]) -> TermRef<'a> {
        TermRef { components }
    }

    /// Convert this reference to an owned Term by cloning the components.
    pub fn to_owned(&self) -> Term {
        // Validate that the result will be a valid Term
        if self.components.is_empty() {
            panic!("Cannot convert empty TermRef to Term");
        }
        if let TermComponent::Composite { span } = self.components[0] {
            panic!(
                "TermRef starts with Composite (span={}) - cannot convert to Term. Components: {:?}",
                span, self.components
            );
        }
        Term {
            components: self.components.to_vec(),
        }
    }

    /// Get the head atom of this term.
    /// The head is always the first component (or first after Composite marker).
    pub fn get_head_atom(&self) -> &Atom {
        match &self.components[0] {
            TermComponent::Atom(atom) => atom,
            TermComponent::Composite { span } => {
                panic!(
                    "Term should not start with Composite marker. Components: {:?}, span: {}",
                    self.components, span
                )
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
            Atom::Variable(i) => local_context.get_var_type(*i as usize).unwrap_or_else(|| {
                panic!(
                    "Variable x{} not found in LocalContext (size={}). TermRef components: {:?}",
                    i,
                    local_context.len(),
                    self.components
                )
            }),
            Atom::Symbol(symbol) => kernel_context.symbol_table.get_type(*symbol),
            Atom::True => BOOL,
        }
    }

    /// Check if this term contains a variable with the given index anywhere.
    pub fn has_variable(&self, index: AtomId) -> bool {
        for component in self.components {
            if let TermComponent::Atom(Atom::Variable(i)) = component {
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
            if let TermComponent::Atom(atom) = component {
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
            if let TermComponent::Atom(atom) = component {
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
            if let TermComponent::Atom(Atom::Symbol(Symbol::Synthetic(_))) = component {
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
            if let TermComponent::Atom(Atom::True) = component {
                continue; // "true" counts as 0
            }
            if matches!(component, TermComponent::Atom(_)) {
                count += 1;
            }
        }
        count
    }

    /// Returns true if this term has any arguments.
    /// This is O(1) unlike num_args() which must iterate.
    pub fn has_args(&self) -> bool {
        self.components.len() > 1
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
            if let TermComponent::Composite { span } = self.components[i] {
                i += span as usize;
            } else {
                i += 1;
            }
        }
        arg_count
    }

    /// Iterate over the arguments of this term without allocating.
    /// Each argument is returned as a TermRef.
    pub fn iter_args(&self) -> TermRefArgsIterator<'a> {
        TermRefArgsIterator {
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
            if let TermComponent::Atom(atom) = component {
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
                TermComponent::Composite { .. } => {
                    // Composite markers don't contribute to weight
                }
                TermComponent::Atom(Atom::True) => {
                    // True doesn't contribute to weight
                }
                TermComponent::Atom(Atom::Variable(i)) => {
                    while refcounts.len() <= *i as usize {
                        refcounts.push(0);
                    }
                    refcounts[*i as usize] += 1;
                }
                TermComponent::Atom(Atom::Symbol(Symbol::GlobalConstant(i))) => {
                    weight1 += 1;
                    weight2 += 4 * (*i) as u32;
                }
                TermComponent::Atom(Atom::Symbol(Symbol::ScopedConstant(i))) => {
                    weight1 += 1;
                    weight2 += 1 + 4 * (*i) as u32;
                }
                TermComponent::Atom(Atom::Symbol(Symbol::Monomorph(i))) => {
                    weight1 += 1;
                    weight2 += 2 + 4 * (*i) as u32;
                }
                TermComponent::Atom(Atom::Symbol(Symbol::Synthetic(i))) => {
                    weight1 += 1;
                    weight2 += 3 + 4 * (*i) as u32;
                }
            }
        }

        (weight1, weight2)
    }

    /// KBO helper that can skip the domination check.
    fn kbo_helper(&self, other: &TermRef, check_domination: bool) -> std::cmp::Ordering {
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
    fn partial_tiebreak(&self, other: &TermRef) -> std::cmp::Ordering {
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
    fn total_tiebreak(&self, other: &TermRef) -> std::cmp::Ordering {
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
    pub fn kbo_cmp(&self, other: &TermRef) -> std::cmp::Ordering {
        self.kbo_helper(other, true)
    }

    /// Extended KBO comparison - total ordering where only identical terms are equal.
    pub fn extended_kbo_cmp(&self, other: &TermRef) -> std::cmp::Ordering {
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

impl fmt::Display for TermRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Format the term by walking through components
        format_term_at(f, self.components, 0)
    }
}

/// Helper function to format a term starting at the given position.
/// Returns the position after the formatted term.
fn format_term_at(f: &mut fmt::Formatter, components: &[TermComponent], pos: usize) -> fmt::Result {
    if pos >= components.len() {
        return Ok(());
    }

    match &components[pos] {
        TermComponent::Composite { span } => {
            // This shouldn't happen at the start of a term, but handle it
            // by formatting the contents (skip the Composite marker)
            let end = pos + *span as usize;
            format_composite_contents(f, components, pos + 1, end)
        }
        TermComponent::Atom(atom) => {
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
    components: &[TermComponent],
    pos: usize,
) -> Result<usize, fmt::Error> {
    match &components[pos] {
        TermComponent::Composite { span } => {
            // Format the composite subterm
            let end = pos + *span as usize;
            format_composite_contents(f, components, pos + 1, end)?;
            Ok(end)
        }
        TermComponent::Atom(atom) => {
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
    components: &[TermComponent],
    start: usize,
    end: usize,
) -> fmt::Result {
    if start >= end {
        return Ok(());
    }

    // The first element after Composite marker is the head
    match &components[start] {
        TermComponent::Atom(atom) => match atom {
            Atom::Variable(i) => write!(f, "x{}", i)?,
            _ => write!(f, "{}", atom)?,
        },
        TermComponent::Composite { .. } => {
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

/// A Term stores term structure without embedding type information.
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
pub struct Term {
    components: Vec<TermComponent>,
}

impl Term {
    /// Create a new Term.
    /// The term_type and head_type parameters are ignored since Term stores types externally.
    pub fn new(_term_type: TypeId, _head_type: TypeId, head: Atom, args: Vec<Term>) -> Term {
        let mut components = vec![TermComponent::Atom(head)];
        for (i, arg) in args.iter().enumerate() {
            // Validate that arg is a valid term (starts with Atom)
            if arg.components.is_empty() {
                panic!("Term::new: arg {} is empty", i);
            }
            if let TermComponent::Composite { span } = arg.components[0] {
                panic!(
                    "Term::new: arg {} starts with Composite (span={}). Arg components: {:?}",
                    i, span, arg.components
                );
            }

            if arg.components.len() == 1 {
                // Atomic argument - just add the atom
                components.push(arg.components[0]);
            } else {
                // Compound argument - add Composite marker with span
                components.push(TermComponent::Composite {
                    span: arg.components.len() as u16 + 1,
                });
                components.extend(arg.components.iter().copied());
            }
        }
        Term { components }
    }

    /// Create a new Term from a vector of components.
    pub fn from_components(components: Vec<TermComponent>) -> Term {
        // Validate structure: must start with Atom, and after each Composite must come an Atom
        if components.is_empty() {
            panic!("from_components: empty components");
        }
        if let TermComponent::Composite { span } = components[0] {
            panic!(
                "from_components: starts with Composite (span={}). Components: {:?}",
                span, components
            );
        }
        // Validate that after each Composite comes an Atom
        for i in 0..components.len() {
            if let TermComponent::Composite { .. } = components[i] {
                if i + 1 >= components.len() {
                    panic!(
                        "from_components: Composite at {} has no following component. Components: {:?}",
                        i, components
                    );
                }
                if let TermComponent::Composite { span: inner } = components[i + 1] {
                    panic!(
                        "from_components: Composite at {} followed by Composite (span={}). Components: {:?}",
                        i, inner, components
                    );
                }
            }
        }
        Term { components }
    }

    /// Create a Term representing a single atom with no arguments.
    /// The type_id parameter is ignored since Term stores types separately.
    pub fn atom(_type_id: TypeId, atom: Atom) -> Term {
        Term {
            components: vec![TermComponent::Atom(atom)],
        }
    }

    /// Parse a Term from a string representation.
    /// Format: "f(a, g(b))" or just "x0" for atoms.
    /// Variables are written as x0, x1, etc.
    /// Constants are written as c0, c1, etc.
    pub fn parse(s: &str) -> Term {
        let s = s.trim();

        if s == "true" {
            return Term::atom(BOOL, Atom::True);
        }

        let first_paren = match s.find('(') {
            Some(i) => i,
            None => return Term::atom(EMPTY, Atom::new(s)),
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
            args.push(Term::parse(&s[start..*terminator_index]));
        }

        // Build the component vector
        let mut components = vec![TermComponent::Atom(Atom::new(head))];
        for arg in args {
            if arg.components.len() == 1 {
                // Atomic argument - just add the atom
                components.push(arg.components[0]);
            } else {
                // Compound argument - add Composite marker with span
                components.push(TermComponent::Composite {
                    span: arg.components.len() as u16 + 1,
                });
                components.extend(arg.components);
            }
        }

        Term { components }
    }

    /// Parse a term string with proper types from context.
    /// For tests that need properly typed terms.
    #[cfg(test)]
    pub fn parse_with_context(
        s: &str,
        _local_context: &LocalContext,
        _kernel_context: &KernelContext,
    ) -> Term {
        // Term doesn't store types internally, so we can use the same parse logic.
        // The types will be looked up from context when needed.
        Term::parse(s)
    }

    /// Get the components of this term.
    pub fn components(&self) -> &[TermComponent] {
        &self.components
    }

    /// Get a borrowed reference to this term.
    pub fn as_ref(&self) -> TermRef {
        TermRef::new(&self.components)
    }

    /// Get the head atom of this term.
    pub fn get_head_atom(&self) -> &Atom {
        match &self.components[0] {
            TermComponent::Atom(atom) => atom,
            TermComponent::Composite { span } => {
                panic!(
                    "Term should not start with Composite marker. Components: {:?}, span: {}",
                    self.components, span
                )
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
        self.as_ref()
            .get_term_type_with_context(local_context, kernel_context)
    }

    /// Get the head type with context.
    /// Uses LocalContext for variable types and KernelContext for symbol types.
    pub fn get_head_type_with_context(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> TypeId {
        self.as_ref()
            .get_head_type_with_context(local_context, kernel_context)
    }

    /// Check if this term is atomic (no arguments).
    pub fn is_atomic(&self) -> bool {
        self.as_ref().is_atomic()
    }

    /// Check if this term is the boolean constant "true".
    pub fn is_true(&self) -> bool {
        self.as_ref().is_true()
    }

    /// Create a new Term representing the boolean constant "true".
    pub fn new_true() -> Term {
        Term::atom(BOOL, Atom::True)
    }

    /// Create a new Term representing a variable with the given index.
    /// The type_id parameter is ignored since Term stores types separately in the context.
    pub fn new_variable(_type_id: TypeId, index: AtomId) -> Term {
        Term {
            components: vec![TermComponent::Atom(Atom::Variable(index))],
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

    /// Returns true if this term has any arguments.
    /// This is O(1) unlike num_args() which must iterate.
    pub fn has_args(&self) -> bool {
        self.components.len() > 1
    }

    /// Get the number of arguments this term has.
    pub fn num_args(&self) -> usize {
        self.as_ref().num_args()
    }

    /// Iterate over the arguments of this term without allocating.
    /// Each argument is returned as a TermRef.
    pub fn iter_args(&self) -> TermRefArgsIterator {
        self.as_ref().iter_args()
    }

    /// Get the arguments of this term as owned Terms.
    /// This allocates a new vector, unlike iter_args() which borrows.
    pub fn args(&self) -> Vec<Term> {
        self.iter_args().map(|arg| arg.to_owned()).collect()
    }

    /// Get a specific argument by index.
    pub fn get_arg(&self, index: usize) -> Option<Term> {
        self.iter_args().nth(index).map(|arg| arg.to_owned())
    }

    /// Iterate over all atoms in the term.
    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom> + '_ {
        self.components.iter().filter_map(|component| {
            if let TermComponent::Atom(atom) = component {
                Some(atom)
            } else {
                None
            }
        })
    }

    /// Returns the head of this term as a Term with no arguments.
    pub fn get_head_term(&self) -> Term {
        Term {
            components: vec![TermComponent::Atom(*self.get_head_atom())],
        }
    }

    /// Collects all variables in the term (recursively through arguments).
    /// Returns (AtomId, TypeId) pairs for each variable found.
    /// Uses the local_context to look up variable types.
    pub fn collect_vars(&self, local_context: &LocalContext) -> Vec<(AtomId, TypeId)> {
        let mut result = Vec::new();
        for atom in self.iter_atoms() {
            if let Atom::Variable(id) = atom {
                let type_id = local_context.get_var_type(*id as usize).unwrap_or_else(|| {
                    panic!(
                        "Variable x{} not found in local context (context has {} types). Term: {}",
                        id,
                        local_context.len(),
                        self
                    )
                });
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
    pub fn replace_variable(&self, id: AtomId, value: &Term) -> Term {
        // Validate input term is well-formed
        for i in 0..self.components.len() {
            if let TermComponent::Composite { .. } = self.components[i] {
                if i + 1 < self.components.len() {
                    if let TermComponent::Composite { span } = self.components[i + 1] {
                        panic!(
                            "replace_variable: input term has Composite followed by Composite at {}. \
                             span={}, components: {:?}",
                            i, span, self.components
                        );
                    }
                }
            }
        }

        // Special case: if this term IS the variable being replaced, just return the value
        if self.components.len() == 1 {
            if let TermComponent::Atom(Atom::Variable(var_id)) = self.components[0] {
                if var_id == id {
                    return value.clone();
                }
            }
        }

        // Build the result by processing components, tracking size changes for spans
        let mut result = Vec::new();
        self.replace_variable_recursive(&mut result, id, value);
        Term::from_components(result)
    }

    /// Helper for replace_variable that processes components recursively.
    /// Returns the number of components added to result.
    fn replace_variable_recursive(
        &self,
        result: &mut Vec<TermComponent>,
        id: AtomId,
        value: &Term,
    ) -> usize {
        let mut i = 0;
        let mut added = 0;

        while i < self.components.len() {
            match &self.components[i] {
                TermComponent::Atom(Atom::Variable(var_id)) if *var_id == id => {
                    // Replace this variable with the value's components
                    if value.components.len() == 1 {
                        // Simple replacement - just copy the single component
                        result.push(value.components[0]);
                        added += 1;
                    } else if i == 0 {
                        // Head position replacement - don't wrap in Composite
                        // The value's head becomes this term's head, and value's args
                        // are inserted before the remaining args
                        result.extend(value.components.iter().copied());
                        added += value.components.len();
                    } else {
                        // Non-head position - need to wrap in Composite
                        result.push(TermComponent::Composite {
                            span: value.components.len() as u16 + 1,
                        });
                        result.extend(value.components.iter().copied());
                        added += value.components.len() + 1;
                    }
                    i += 1;
                }
                TermComponent::Atom(atom) => {
                    // Non-matching atom - copy as-is
                    result.push(TermComponent::Atom(*atom));
                    added += 1;
                    i += 1;
                }
                TermComponent::Composite { span } => {
                    // Process the composite subterm recursively
                    let subterm_start = i + 1;
                    let subterm_end = i + *span as usize;

                    // Create a temporary Term for the subterm (excluding Composite marker)
                    let subterm =
                        Term::from_components(self.components[subterm_start..subterm_end].to_vec());

                    // Recursively replace in the subterm
                    let mut sub_result = Vec::new();
                    subterm.replace_variable_recursive(&mut sub_result, id, value);

                    // Validate: sub_result must start with Atom, not Composite
                    if let Some(TermComponent::Composite { span: sr_span }) = sub_result.first() {
                        panic!(
                            "replace_variable_recursive: sub_result starts with Composite (span={}). \
                             Original subterm: {:?}, sub_result: {:?}",
                            sr_span, subterm.components, sub_result
                        );
                    }

                    // If the subterm is now atomic (single component), don't wrap it
                    if sub_result.len() == 1 {
                        result.push(sub_result[0]);
                        added += 1;
                    } else {
                        // Add a new Composite marker with the correct span
                        result.push(TermComponent::Composite {
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
    pub fn replace_variables(&self, var_ids: &[AtomId], replacement_terms: &[&Term]) -> Term {
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
    pub fn replace_atom(&self, old_atom: &Atom, new_atom: &Atom) -> Term {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                TermComponent::Atom(atom) if atom == old_atom => TermComponent::Atom(*new_atom),
                c => *c,
            })
            .collect();
        Term::from_components(new_components)
    }

    /// Renumbers synthetic atoms from the provided list into the invalid range.
    pub fn invalidate_synthetics(&self, from: &[AtomId]) -> Term {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                TermComponent::Atom(atom) => TermComponent::Atom(atom.invalidate_synthetics(from)),
                c => *c,
            })
            .collect();
        Term::from_components(new_components)
    }

    /// Replace the first `num_to_replace` variables with invalid synthetic atoms, adjusting
    /// the subsequent variable ids accordingly.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> Term {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                TermComponent::Atom(atom) => {
                    TermComponent::Atom(atom.instantiate_invalid_synthetics(num_to_replace))
                }
                c => *c,
            })
            .collect();
        Term::from_components(new_components)
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
            if let TermComponent::Atom(Atom::Variable(i)) = component {
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
    pub fn remap_variables(&self, var_map: &[AtomId]) -> Term {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                TermComponent::Atom(atom) => TermComponent::Atom(atom.remap_variables(var_map)),
                c => *c,
            })
            .collect();
        Term::from_components(new_components)
    }

    /// Build a term from a spine (function + arguments).
    /// If the spine has one element, returns just that element.
    /// Otherwise, treats the first element as the function and the rest as arguments.
    /// The term_type parameter is ignored since Term stores types externally.
    pub fn from_spine(mut spine: Vec<Term>, _term_type: TypeId) -> Term {
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
            let mut components = vec![TermComponent::Atom(*func.get_head_atom())];
            for arg in all_args {
                if arg.components.len() == 1 {
                    components.push(arg.components[0]);
                } else {
                    components.push(TermComponent::Composite {
                        span: arg.components.len() as u16 + 1,
                    });
                    components.extend(arg.components.iter().copied());
                }
            }
            Term::from_components(components)
        }
    }

    /// Apply additional arguments to this term.
    /// The result_type parameter is ignored since Term stores types externally.
    pub fn apply(&self, args: &[Term], _result_type: TypeId) -> Term {
        if args.is_empty() {
            return self.clone();
        }

        let mut components = self.components.clone();
        for arg in args {
            if arg.components.len() == 1 {
                components.push(arg.components[0]);
            } else {
                components.push(TermComponent::Composite {
                    span: arg.components.len() as u16 + 1,
                });
                components.extend(arg.components.iter().copied());
            }
        }
        Term::from_components(components)
    }

    /// Replace all arguments with new arguments.
    pub fn replace_args(&self, new_args: Vec<Term>) -> Term {
        let mut components = vec![TermComponent::Atom(*self.get_head_atom())];
        for arg in new_args {
            if arg.components.len() == 1 {
                components.push(arg.components[0]);
            } else {
                components.push(TermComponent::Composite {
                    span: arg.components.len() as u16 + 1,
                });
                components.extend(arg.components.iter().copied());
            }
        }
        Term::from_components(components)
    }

    /// Knuth-Bendix partial reduction ordering.
    /// Returns Greater if self > other, Less if other > self.
    /// Returns Equal if they cannot be ordered (not equality in the usual sense).
    pub fn kbo_cmp(&self, other: &Term) -> std::cmp::Ordering {
        self.as_ref().kbo_cmp(&other.as_ref())
    }

    /// Extended KBO comparison - total ordering where only identical terms are equal.
    pub fn extended_kbo_cmp(&self, other: &Term) -> std::cmp::Ordering {
        self.as_ref().extended_kbo_cmp(&other.as_ref())
    }

    /// Normalize variable IDs in place so they appear in order of first occurrence.
    /// The var_ids vector tracks which original variable IDs have been seen.
    /// This mutates the term in place.
    pub fn normalize_var_ids(&mut self, var_ids: &mut Vec<AtomId>) {
        for component in &mut self.components {
            if let TermComponent::Atom(Atom::Variable(i)) = component {
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
    pub fn get_term_at_path(&self, path: &[usize]) -> Option<Term> {
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
                TermComponent::Composite { span } => {
                    current_pos += span as usize;
                }
                TermComponent::Atom(_) => {
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
            TermComponent::Composite { span } => {
                // The argument spans from current_pos to current_pos + span
                // But the Composite marker isn't part of the term's components, so skip it
                Term::from_components(
                    self.components[current_pos + 1..current_pos + span as usize].to_vec(),
                )
            }
            TermComponent::Atom(atom) => Term::from_components(vec![TermComponent::Atom(atom)]),
        };

        // Recurse for the rest of the path
        arg.get_term_at_path(&path[1..])
    }

    /// Replace the subterm at the given path with a replacement.
    /// A path is a sequence of argument indices to follow.
    /// An empty path replaces the whole term.
    pub fn replace_at_path(&self, path: &[usize], replacement: Term) -> Term {
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
                TermComponent::Composite { span } => current_pos + span as usize,
                TermComponent::Atom(_) => current_pos + 1,
            };

            if current_arg == arg_index {
                // This is the argument to replace (or recurse into)
                let old_arg = match self.components[arg_start] {
                    TermComponent::Composite { span } => Term::from_components(
                        self.components[arg_start + 1..arg_start + span as usize].to_vec(),
                    ),
                    TermComponent::Atom(atom) => {
                        Term::from_components(vec![TermComponent::Atom(atom)])
                    }
                };

                let new_arg = old_arg.replace_at_path(&path[1..], replacement.clone());

                // Add the new argument to components
                if new_arg.components.len() == 1 {
                    new_components.push(new_arg.components[0]);
                } else {
                    new_components.push(TermComponent::Composite {
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

        Term::from_components(new_components)
    }

    /// Find all rewritable subterms with their paths.
    /// It is an error to call this on any variables.
    /// Any term is rewritable except for "true".
    pub fn rewritable_subterms(&self) -> Vec<(Vec<usize>, Term)> {
        let mut answer = vec![];
        let mut prefix = vec![];
        self.push_rewritable_subterms(&mut prefix, &mut answer);
        answer
    }

    /// Helper for rewritable_subterms.
    fn push_rewritable_subterms(
        &self,
        prefix: &mut Vec<usize>,
        answer: &mut Vec<(Vec<usize>, Term)>,
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

impl fmt::Display for Term {
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

/// Iterator over the arguments of a TermRef, yielding borrowed references.
pub struct TermRefArgsIterator<'a> {
    components: &'a [TermComponent],
    position: usize,
}

impl<'a> Iterator for TermRefArgsIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position >= self.components.len() {
            return None;
        }

        match self.components[self.position] {
            TermComponent::Composite { span } => {
                // Extract the composite term as a slice reference.
                // Skip the Composite marker itself - the term content starts after it.
                let start = self.position + 1;
                let end = self.position + span as usize;
                if end > self.components.len() {
                    panic!(
                        "iter_args: span {} at position {} exceeds components length {}. Components: {:?}",
                        span, self.position, self.components.len(), self.components
                    );
                }
                let arg_slice = &self.components[start..end];
                // Validate the extracted slice starts with an Atom
                if !arg_slice.is_empty() {
                    if let TermComponent::Composite { span: inner_span } = arg_slice[0] {
                        panic!(
                            "iter_args: extracted arg starts with Composite (inner_span={}). \
                             Parent components: {:?}, position: {}, span: {}, arg_slice: {:?}",
                            inner_span, self.components, self.position, span, arg_slice
                        );
                    }
                }
                self.position += span as usize;
                Some(TermRef::new(arg_slice))
            }
            TermComponent::Atom(_) => {
                // Simple atomic argument as a single-element slice
                let arg_slice = &self.components[self.position..self.position + 1];
                self.position += 1;
                Some(TermRef::new(arg_slice))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::symbol::Symbol;

    #[test]
    fn test_replace_head_variable_with_compound_term() {
        // This tests the bug where replacing a variable at head position with a
        // compound term incorrectly wrapped the result in a Composite marker.
        //
        // Term: x0(x1) - variable x0 applied to x1
        // Replace x0 with m0(c0) - a compound term
        // Expected result: m0(c0, x1) - m0 applied to c0 and x1
        // Bug would produce: [Composite, m0, c0, x1] which is invalid
        let term = Term::parse("x0(x1)");
        let replacement = Term::parse("m0(c0)");

        // Replace x0 with m0(c0)
        let result = term.replace_variable(0, &replacement);

        // Result should be m0(c0, x1)
        // This should not panic due to invalid term structure
        let head = result.get_head_atom();
        assert!(matches!(head, Atom::Symbol(Symbol::Monomorph(0))));

        // The result should have exactly two args: c0 and x1
        let args: Vec<_> = result.iter_args().collect();
        assert_eq!(args.len(), 2, "Expected 2 args, got {}", args.len());

        // First arg should be c0
        let arg0_head = args[0].get_head_atom();
        assert!(matches!(arg0_head, Atom::Symbol(Symbol::ScopedConstant(0))));

        // Second arg should be x1
        let arg1_head = args[1].get_head_atom();
        assert!(matches!(arg1_head, Atom::Variable(1)));
    }

    #[test]
    fn test_replace_head_variable_simple() {
        // Simpler case: x0(x1) with x0 -> c0 (atomic replacement)
        let term = Term::parse("x0(x1)");
        let replacement = Term::parse("c0");

        let result = term.replace_variable(0, &replacement);

        // Result should be c0(x1)
        let head = result.get_head_atom();
        assert!(matches!(head, Atom::Symbol(Symbol::ScopedConstant(0))));

        let args: Vec<_> = result.iter_args().collect();
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0].get_head_atom(), Atom::Variable(1)));
    }

    #[test]
    fn test_replace_non_head_variable_with_compound() {
        // Non-head position should still wrap in Composite
        // Term: c0(x0) - c0 applied to variable x0
        // Replace x0 with m0(c1) - a compound term
        // Result: c0(m0(c1)) - c0 applied to m0(c1)
        let term = Term::parse("c0(x0)");
        let replacement = Term::parse("m0(c1)");

        let result = term.replace_variable(0, &replacement);

        // Result should be c0(m0(c1))
        let head = result.get_head_atom();
        assert!(matches!(head, Atom::Symbol(Symbol::ScopedConstant(0))));

        let args: Vec<_> = result.iter_args().collect();
        assert_eq!(args.len(), 1);

        // The arg should be compound: m0(c1)
        let arg = &args[0];
        let arg_head = arg.get_head_atom();
        assert!(matches!(arg_head, Atom::Symbol(Symbol::Monomorph(0))));
    }

    #[test]
    fn test_nested_term_comparison() {
        // Create nested terms like f(g(a)) and f(g(b))
        // This exercises iter_args() and partial_tiebreak on composite arguments
        let term1 = Term::parse("c0(c1(c2))");
        let term2 = Term::parse("c0(c1(c3))");

        // This should not panic - it exercises the code path where
        // iter_args returns a TermRef for a composite argument
        let _ = term1.extended_kbo_cmp(&term2);
    }

    #[test]
    fn test_iter_args_on_nested_term() {
        // f(g(a), b) has two args: g(a) which is composite, and b which is atomic
        let term = Term::parse("c0(c1(c2), c3)");

        let args: Vec<_> = term.iter_args().collect();
        assert_eq!(args.len(), 2);

        // Each arg should be able to get its head atom without panicking
        for arg in &args {
            let _ = arg.get_head_atom();
        }
    }
}
