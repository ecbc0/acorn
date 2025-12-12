use serde::{Deserialize, Serialize};
use std::fmt;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::closed_type::ClosedType;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;

/// A step in a path through a term.
/// Treats applications in curried form: f(a, b) becomes ((f a) b).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PathStep {
    /// Go to the function part of an application
    Function,
    /// Go to the argument part of an application
    Argument,
}

/// A component of a Term or ClosedType in its flattened representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Serialize, Deserialize)]
pub enum TermComponent {
    /// Indicates a function application with the given span (total number of components).
    /// The span includes this Application marker itself, the head, and all arguments recursively.
    /// To skip over this entire subterm: index += span
    /// To enter this subterm (process the head): index += 1
    /// Used in Term (open terms with free variables).
    Application { span: u16 },

    /// A Pi type (dependent function type) with the given span.
    /// The span includes this Pi marker, the binder type, and the body.
    /// Pi always has exactly 2 sub-elements: binder type and body.
    /// Used in ClosedType to represent types like `(T : Type<CommRing>) -> T -> T -> T`.
    /// A non-dependent arrow `A -> B` is represented as `Pi(A, B)` where B doesn't use Var(0).
    Pi { span: u16 },

    /// A leaf atom in the term tree.
    Atom(Atom),
}

/// Decomposition of a term into its lambda-calculus structure.
/// This provides a cleaner way to pattern match on terms without dealing with
/// "head + N arguments" representations.
#[derive(Clone, Copy, Debug)]
pub enum Decomposition<'a> {
    /// An atomic term with no arguments.
    Atom(&'a Atom),

    /// A curried application: (func arg).
    /// For f(a, b, c), decomposes into (f(a, b), c).
    Application(TermRef<'a>, TermRef<'a>),
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

    /// Get the underlying components slice (for debugging/validation).
    pub fn components(&self) -> &[TermComponent] {
        self.components
    }

    /// Convert this reference to an owned Term by cloning the components.
    /// Note: This preserves the format of the slice (old or new).
    /// Use Term::new() or similar constructors if you need new-format terms.
    pub fn to_owned(&self) -> Term {
        if self.components.is_empty() {
            panic!("Cannot convert empty TermRef to Term");
        }
        Term {
            components: self.components.to_vec(),
        }
    }

    /// Get the head atom of this term.
    /// The head is always the first component (or first after Application marker).
    pub fn get_head_atom(&self) -> &Atom {
        match &self.components[0] {
            TermComponent::Atom(atom) => atom,
            TermComponent::Application { .. } => {
                // Skip the Application marker to get the head
                match &self.components[1] {
                    TermComponent::Atom(atom) => atom,
                    _ => panic!(
                        "Expected Atom after Application marker. Components: {:?}",
                        self.components
                    ),
                }
            }
            TermComponent::Pi { span } => {
                panic!(
                    "Term should not start with Pi marker. Components: {:?}, span: {}",
                    self.components, span
                )
            }
        }
    }

    /// Check if this term is atomic (no arguments).
    pub fn is_atomic(&self) -> bool {
        self.components.len() == 1
    }

    /// Decompose this term into its fundamental lambda-calculus structure.
    ///
    /// Returns either:
    /// - `Decomposition::Atom(&atom)` if the term is atomic
    /// - `Decomposition::Application(func, arg)` if the term is an application
    ///
    /// This provides a cleaner way to write recursive algorithms on terms
    /// by pattern matching on the structure rather than checking multiple conditions.
    pub fn decompose(&self) -> Decomposition<'a> {
        // Handle atomic terms (single Atom, no Application wrapper)
        if self.components.len() == 1 {
            let atom = match &self.components[0] {
                TermComponent::Atom(atom) => atom,
                _ => panic!("atomic term should have Atom component"),
            };
            return Decomposition::Atom(atom);
        }

        // Determine the bounds based on whether we have an Application wrapper
        let (args_start, args_end) = match self.components[0] {
            TermComponent::Application { span } => (2, span as usize), // Skip App marker and head
            TermComponent::Atom(_) => (1, self.components.len()),      // Old format: skip head only
            TermComponent::Pi { .. } => panic!("Pi should not appear in term structure"),
        };

        // Find the start of the last argument
        let mut prev_position = args_start;
        let mut position = args_start;

        while position < args_end {
            prev_position = position;
            if position >= self.components.len() {
                panic!(
                    "decompose: position {} >= len {}. components: {:?}, args_start: {}, args_end: {}",
                    position, self.components.len(), self.components, args_start, args_end
                );
            }
            match self.components[position] {
                TermComponent::Application { span } => {
                    position += span as usize;
                }
                TermComponent::Atom(_) => {
                    position += 1;
                }
                TermComponent::Pi { .. } => {
                    panic!("Pi should not appear in term structure");
                }
            }
        }

        // prev_position now points to the start of the last argument
        // Build the func_part: everything except the last argument
        let func_part = if prev_position == args_start {
            // Only one argument - func_part is just the head atom
            match self.components[0] {
                TermComponent::Application { .. } => {
                    // Head is at position 1
                    TermRef::new(&self.components[1..2])
                }
                TermComponent::Atom(_) => {
                    // Head is at position 0
                    TermRef::new(&self.components[0..1])
                }
                _ => panic!("Unexpected component"),
            }
        } else {
            // Multiple arguments - need to build func_part with remaining args
            match self.components[0] {
                TermComponent::Application { .. } => {
                    // Reconstruct: [Application{span}, head, args_except_last]
                    // We return a slice from 0 to prev_position, but with adjusted span
                    // Actually, we can just return the slice - it already has the right structure
                    // But we need to handle the span adjustment... this is tricky for zero-copy.
                    // For now, return the slice as-is; the span will be wrong but we're removing
                    // the outer Application wrapper anyway.
                    // Actually, the func_part should NOT include the outer Application wrapper.
                    // It should be: [Application{new_span}, head, args_except_last] or [head, args_except_last]
                    // For zero-copy, we return [head, args_except_last] (old format)
                    TermRef::new(&self.components[1..prev_position])
                }
                TermComponent::Atom(_) => {
                    // Old format: just slice up to prev_position
                    TermRef::new(&self.components[..prev_position])
                }
                _ => panic!("Unexpected component"),
            }
        };

        // Extract the last argument
        let last_arg = match self.components[prev_position] {
            TermComponent::Application { span } => {
                // Composite argument - return the whole slice (with Application wrapper)
                let end = prev_position + span as usize;
                TermRef::new(&self.components[prev_position..end])
            }
            TermComponent::Atom(_) => {
                // Simple atomic argument
                TermRef::new(&self.components[prev_position..prev_position + 1])
            }
            TermComponent::Pi { .. } => {
                panic!("Pi should not appear in term structure");
            }
        };

        Decomposition::Application(func_part, last_arg)
    }

    /// Split an application into (function, argument) in curried form.
    /// For f(a, b, c), returns (f(a, b), c).
    /// Returns None if the term is atomic (has no arguments).
    ///
    /// Both returned TermRefs are slices of the original - no allocation.
    pub fn split_application(&self) -> Option<(TermRef<'a>, TermRef<'a>)> {
        match self.decompose() {
            Decomposition::Atom(_) => None,
            Decomposition::Application(func, arg) => Some((func, arg)),
        }
    }

    /// Check if this term is the boolean constant "true".
    pub fn is_true(&self) -> bool {
        matches!(self.get_head_atom(), Atom::Symbol(Symbol::True))
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

    /// Get the term's ClosedType with context.
    /// Uses LocalContext for variable types and KernelContext for symbol types.
    /// For function applications, recursively gets the function's type and applies it.
    pub fn get_closed_type_with_context(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> ClosedType {
        match self.decompose() {
            Decomposition::Atom(atom) => match atom {
                Atom::Variable(i) => local_context
                    .get_var_closed_type(*i as usize)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "Variable x{} not found in LocalContext (size={}). TermRef components: {:?}",
                            i,
                            local_context.len(),
                            self.components
                        )
                    }),
                Atom::Symbol(symbol) => kernel_context.symbol_table.get_closed_type(*symbol).clone(),
            },
            Decomposition::Application(func, _arg) => {
                // The function has type A -> B, so the application has type B
                let func_type = func.get_closed_type_with_context(local_context, kernel_context);
                func_type
                    .apply()
                    .expect("Function type expected but not found during type application")
            }
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

    /// Count the number of atom components (excluding Application markers).
    pub fn atom_count(&self) -> u32 {
        let mut count = 0;
        for component in self.components {
            // True and False count as 0
            if matches!(
                component,
                TermComponent::Atom(Atom::Symbol(Symbol::True))
                    | TermComponent::Atom(Atom::Symbol(Symbol::False))
            ) {
                continue;
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
        // A term has args if it starts with Application, or if it's old format with len > 1
        match self.components[0] {
            TermComponent::Application { .. } => true,
            TermComponent::Atom(_) => self.components.len() > 1,
            TermComponent::Pi { .. } => panic!("Pi should not appear in Term"),
        }
    }

    /// Get the number of arguments this term has.
    pub fn num_args(&self) -> usize {
        // Determine where arguments start based on whether we have an Application wrapper
        let (args_start, args_end) = match self.components[0] {
            TermComponent::Application { span } => (2, span as usize), // Skip App marker and head
            TermComponent::Atom(_) => {
                if self.components.len() <= 1 {
                    return 0;
                }
                (1, self.components.len()) // Skip head atom only
            }
            TermComponent::Pi { .. } => panic!("Pi should not appear in Term"),
        };

        let mut arg_count = 0;
        let mut i = args_start;
        while i < args_end {
            arg_count += 1;
            if let TermComponent::Application { span } = self.components[i] {
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
        // Determine the start and end positions for iteration
        let (start, end) = match self.components[0] {
            TermComponent::Application { span } => (2, span as usize), // Skip App marker and head
            TermComponent::Atom(_) => {
                if self.components.len() <= 1 {
                    return TermRefArgsIterator {
                        components: self.components,
                        position: self.components.len(),
                        end: self.components.len(),
                    };
                }
                (1, self.components.len()) // Skip head atom only
            }
            TermComponent::Pi { .. } => panic!("Pi should not appear in Term"),
        };
        TermRefArgsIterator {
            components: self.components,
            position: start,
            end,
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
        let mut weight1 = 0;
        let mut weight2 = 0;

        for component in self.components {
            match component {
                TermComponent::Application { .. } => {
                    // Application markers don't contribute to weight
                }
                TermComponent::Pi { .. } => {
                    panic!("Pi should not appear in Term, only in ClosedType")
                }
                TermComponent::Atom(Atom::Symbol(Symbol::True))
                | TermComponent::Atom(Atom::Symbol(Symbol::False)) => {
                    // True/False don't contribute to weight
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
                TermComponent::Atom(Atom::Symbol(Symbol::Type(_))) => {
                    panic!("Symbol::Type should not appear in Term, only in ClosedType")
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

    /// Navigate to a subterm using a path.
    /// Returns None if the path doesn't exist or we hit an atomic term.
    pub fn get_term_at_path(&self, path: &[PathStep]) -> Option<TermRef<'a>> {
        if path.is_empty() {
            return Some(*self);
        }

        // Try to split the application
        let (func, arg) = self.split_application()?;

        match path[0] {
            PathStep::Argument => arg.get_term_at_path(&path[1..]),
            PathStep::Function => func.get_term_at_path(&path[1..]),
        }
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
        TermComponent::Application { span } => {
            // Term starts with Application marker (new format)
            // Format the contents (skip the Application marker)
            let end = pos + *span as usize;
            format_application_contents(f, components, pos + 1, end)
        }
        TermComponent::Pi { .. } => {
            // Pi shouldn't appear in regular Term formatting
            Err(fmt::Error)
        }
        TermComponent::Atom(atom) => {
            // Format the head atom (old format or atomic term)
            match atom {
                Atom::Variable(i) => write!(f, "x{}", i)?,
                _ => write!(f, "{}", atom)?,
            }
            // Check if there are arguments following (old format)
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
        TermComponent::Application { span } => {
            // Format the application subterm
            let end = pos + *span as usize;
            format_application_contents(f, components, pos + 1, end)?;
            Ok(end)
        }
        TermComponent::Pi { .. } => {
            // Pi shouldn't appear in regular Term formatting
            Err(fmt::Error)
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

/// Format the contents of an application (head + args) from start to end.
fn format_application_contents(
    f: &mut fmt::Formatter,
    components: &[TermComponent],
    start: usize,
    end: usize,
) -> fmt::Result {
    if start >= end {
        return Ok(());
    }

    // The first element after Application marker is the head
    match &components[start] {
        TermComponent::Atom(atom) => match atom {
            Atom::Variable(i) => write!(f, "x{}", i)?,
            _ => write!(f, "{}", atom)?,
        },
        TermComponent::Application { .. } | TermComponent::Pi { .. } => {
            // Nested application/Pi as head - shouldn't normally happen
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
/// - Nested "f(a, g(b))": [Atom(f), Atom(a), Application{span: 3}, Atom(g), Atom(b)]
///                                            ^--- this application has span 3: the marker, g, and b
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Term {
    components: Vec<TermComponent>,
}

impl Term {
    /// Create a new Term with the given head atom and arguments.
    /// If args is empty, returns an atomic term [Atom(head)].
    /// If args is non-empty, wraps in Application: [Application{span}, Atom(head), ...args].
    pub fn new(head: Atom, args: Vec<Term>) -> Term {
        if args.is_empty() {
            return Term {
                components: vec![TermComponent::Atom(head)],
            };
        }

        // Non-atomic: build [Application{span}, head, args...]
        let mut components = vec![
            TermComponent::Application { span: 0 }, // Placeholder, will update
            TermComponent::Atom(head),
        ];

        for (i, arg) in args.iter().enumerate() {
            if arg.components.is_empty() {
                panic!("Term::new: arg {} is empty", i);
            }

            if arg.components.len() == 1 {
                // Atomic argument - just add the atom
                components.push(arg.components[0]);
            } else {
                // Compound argument - check if it has Application wrapper
                match arg.components[0] {
                    TermComponent::Application { span } => {
                        // Already has Application wrapper - copy as-is
                        debug_assert_eq!(
                            span as usize,
                            arg.components.len(),
                            "Term::new: arg {} has Application with wrong span {} (expected {}). Components: {:?}",
                            i,
                            span,
                            arg.components.len(),
                            arg.components
                        );
                        components.extend(arg.components.iter().copied());
                    }
                    TermComponent::Atom(_) => {
                        // Old format - wrap in Application
                        let arg_span = arg.components.len() as u16 + 1;
                        components.push(TermComponent::Application { span: arg_span });
                        components.extend(arg.components.iter().copied());
                    }
                    TermComponent::Pi { .. } => {
                        panic!(
                            "Term::new: arg {} starts with Pi. Components: {:?}",
                            i, arg.components
                        );
                    }
                }
            }
        }

        // Update the outer Application span
        components[0] = TermComponent::Application {
            span: components.len() as u16,
        };
        Term { components }
    }

    /// Create a new Term from a vector of components.
    /// Accepts both old format (starting with Atom) and new format (starting with Application).
    pub fn from_components(components: Vec<TermComponent>) -> Term {
        if components.is_empty() {
            panic!("from_components: empty components");
        }
        // Basic validation: check first component
        match components[0] {
            TermComponent::Application { span } => {
                // New format: must have Atom at position 1
                if components.len() < 2 {
                    panic!(
                        "from_components: Application at start but no head atom. Components: {:?}",
                        components
                    );
                }
                if !matches!(components[1], TermComponent::Atom(_)) {
                    panic!(
                        "from_components: Application at start followed by non-Atom at position 1. Components: {:?}",
                        components
                    );
                }
                if span as usize != components.len() {
                    panic!(
                        "from_components: outer Application span {} doesn't match components length {}. Components: {:?}",
                        span, components.len(), components
                    );
                }
            }
            TermComponent::Atom(_) => {
                // Old format or atomic term - ok
            }
            TermComponent::Pi { .. } => {
                panic!("from_components: Pi should not appear in Term");
            }
        }
        // Note: We don't validate inner structure strictly because old format
        // allows Application followed by Application (for nested compound args).
        // The structure is validated lazily during operations.
        // However, let's add a debug check to catch bad spans
        #[cfg(debug_assertions)]
        {
            let mut i = 0;
            while i < components.len() {
                if let TermComponent::Application { span } = components[i] {
                    let end = i + span as usize;
                    if end > components.len() {
                        panic!(
                            "from_components: Application at {} has span {} but only {} components total. Components: {:?}",
                            i, span, components.len(), components
                        );
                    }
                    i = end;
                } else {
                    i += 1;
                }
            }
        }
        Term { components }
    }

    /// Create a Term representing a single atom with no arguments.
    pub fn atom(atom: Atom) -> Term {
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
            return Term::atom(Atom::Symbol(Symbol::True));
        }
        if s == "false" {
            return Term::atom(Atom::Symbol(Symbol::False));
        }

        let first_paren = match s.find('(') {
            Some(i) => i,
            None => return Term::atom(Atom::new(s)),
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

        // Build the component vector using Term::new
        Term::new(Atom::new(head), args)
    }

    /// Get the components of this term.
    pub fn components(&self) -> &[TermComponent] {
        &self.components
    }

    /// Get a borrowed reference to this term.
    pub fn as_ref(&self) -> TermRef {
        // Debug validation
        #[cfg(debug_assertions)]
        if let TermComponent::Application { span } = self.components[0] {
            if span as usize != self.components.len() {
                panic!(
                    "as_ref: Term has Application at start with span {} but len {}. Components: {:?}",
                    span, self.components.len(), self.components
                );
            }
        }
        TermRef::new(&self.components)
    }

    /// Get the head atom of this term.
    pub fn get_head_atom(&self) -> &Atom {
        match &self.components[0] {
            TermComponent::Atom(atom) => atom,
            TermComponent::Application { .. } => {
                // Skip the Application marker to get the head
                match &self.components[1] {
                    TermComponent::Atom(atom) => atom,
                    _ => panic!(
                        "Expected Atom after Application marker. Components: {:?}",
                        self.components
                    ),
                }
            }
            TermComponent::Pi { span } => {
                panic!(
                    "Term should not start with Pi marker. Components: {:?}, span: {}",
                    self.components, span
                )
            }
        }
    }

    /// Get the term's ClosedType with context.
    /// Uses LocalContext for variable types and KernelContext for symbol types.
    /// For function applications, applies the function type once per argument.
    pub fn get_closed_type_with_context(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> ClosedType {
        self.as_ref()
            .get_closed_type_with_context(local_context, kernel_context)
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
        Term::atom(Atom::Symbol(Symbol::True))
    }

    /// Create a new Term representing the boolean constant "false".
    pub fn new_false() -> Term {
        Term::atom(Atom::Symbol(Symbol::False))
    }

    /// Create a new Term representing a variable with the given index.
    pub fn new_variable(index: AtomId) -> Term {
        Term {
            components: vec![TermComponent::Atom(Atom::Variable(index))],
        }
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

    /// Count the number of atom components (excluding Application markers).
    pub fn atom_count(&self) -> u32 {
        self.as_ref().atom_count()
    }

    /// Returns true if this term has any arguments.
    /// This is O(1) unlike num_args() which must iterate.
    pub fn has_args(&self) -> bool {
        self.as_ref().has_args()
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
    /// Returns (AtomId, ClosedType) pairs for each variable found.
    /// Uses the local_context to look up variable types.
    pub fn collect_vars(&self, local_context: &LocalContext) -> Vec<(AtomId, ClosedType)> {
        let mut result = Vec::new();
        for atom in self.iter_atoms() {
            if let Atom::Variable(id) = atom {
                let closed_type = local_context
                    .get_var_closed_type(*id as usize)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "Variable x{} not found in local context (context has {} types). Term: {}",
                            id,
                            local_context.len(),
                            self
                        )
                    });
                result.push((*id, closed_type));
            }
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
    /// This handles the complexity of updating Application span markers when
    /// the replacement term has a different size than the variable (1 component).
    pub fn replace_variable(&self, id: AtomId, value: &Term) -> Term {
        // Special case: if this term IS the variable being replaced, just return the value
        if self.components.len() == 1 {
            if let TermComponent::Atom(Atom::Variable(var_id)) = self.components[0] {
                if var_id == id {
                    return value.clone();
                }
            }
        }

        // Use a recursive approach based on decomposition
        self.replace_variable_impl(id, value)
    }

    /// Helper for replace_variable using decomposition.
    fn replace_variable_impl(&self, id: AtomId, value: &Term) -> Term {
        match self.as_ref().decompose() {
            Decomposition::Atom(atom) => {
                if let Atom::Variable(var_id) = atom {
                    if *var_id == id {
                        return value.clone();
                    }
                }
                // Not the variable we're replacing, return as-is
                self.clone()
            }
            Decomposition::Application(func_ref, arg_ref) => {
                // Recursively replace in both func and arg parts
                let func = func_ref.to_owned();
                let arg = arg_ref.to_owned();

                let new_func = func.replace_variable_impl(id, value);
                let new_arg = arg.replace_variable_impl(id, value);

                // Rebuild the application
                new_func.apply(&[new_arg])
            }
        }
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

    /// Normalize variable IDs in place.
    /// Renumbers variables to appear in order of first occurrence (0, 1, 2, ...).
    /// The var_ids output tracks original variable IDs for use with LocalContext::remap.
    pub fn normalize_var_ids_into(&mut self, var_ids: &mut Vec<AtomId>) {
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

    /// Apply additional arguments to this term.
    /// Apply this term to a slice of arguments.
    pub fn apply(&self, args: &[Term]) -> Term {
        if args.is_empty() {
            return self.clone();
        }

        // Get existing args and combine with new args
        let existing_args = self.args();
        let mut all_args = existing_args;
        all_args.extend(args.iter().cloned());

        // Use Term::new to build the result with proper Application wrapper
        Term::new(*self.get_head_atom(), all_args)
    }

    /// Build a term from a spine (function + arguments).
    /// If the spine has one element, returns just that element.
    /// Otherwise, treats the first element as the function and the rest as arguments.
    pub fn from_spine(mut spine: Vec<Term>) -> Term {
        if spine.is_empty() {
            panic!("from_spine called with empty spine");
        }

        if spine.len() == 1 {
            spine.pop().unwrap()
        } else {
            let func = spine.remove(0);
            let func_args = func.args();
            let mut all_args = func_args;
            all_args.extend(spine);

            // Use Term::new to build the result with proper Application wrapper
            Term::new(*func.get_head_atom(), all_args)
        }
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
    /// A path uses PathStep::Function/Argument to navigate the curried term structure.
    /// An empty path returns the whole term.
    pub fn get_term_at_path(&self, path: &[PathStep]) -> Option<Term> {
        self.as_ref().get_term_at_path(path).map(|r| r.to_owned())
    }

    /// Replace the subterm at the given path with a replacement.
    /// A path uses PathStep::Function/Argument to navigate the curried term structure.
    /// An empty path replaces the whole term.
    pub fn replace_at_path(&self, path: &[PathStep], replacement: Term) -> Term {
        if path.is_empty() {
            return replacement;
        }

        match path[0] {
            PathStep::Argument => {
                // Replace in the last argument
                match self.as_ref().split_application() {
                    Some((func, arg)) => {
                        let new_arg = arg.to_owned().replace_at_path(&path[1..], replacement);
                        func.to_owned().apply(&[new_arg])
                    }
                    None => panic!("Cannot follow Argument path on atomic term"),
                }
            }
            PathStep::Function => {
                // Replace in the function part (all but last arg)
                match self.as_ref().split_application() {
                    Some((func, arg)) => {
                        let new_func = func.to_owned().replace_at_path(&path[1..], replacement);
                        new_func.apply(&[arg.to_owned()])
                    }
                    None => panic!("Cannot follow Function path on atomic term"),
                }
            }
        }
    }

    /// Find all rewritable subterms with their paths.
    /// A path uses Vec<PathStep> to navigate the curried term structure.
    /// It is an error to call this on any variables.
    /// Any term is rewritable except for "true".
    pub fn rewritable_subterms_with_paths(&self) -> Vec<(Vec<PathStep>, Term)> {
        let mut answer = vec![];
        let mut prefix = vec![];
        self.push_rewritable_subterms_with_paths(&mut prefix, &mut answer);
        answer
    }

    /// Helper for rewritable_subterms_with_paths.
    fn push_rewritable_subterms_with_paths(
        &self,
        prefix: &mut Vec<PathStep>,
        answer: &mut Vec<(Vec<PathStep>, Term)>,
    ) {
        if self.is_true() {
            return;
        }
        if self.is_variable() {
            panic!("expected no variables");
        }

        // In the curried view, we navigate using Function/Argument.
        // For a term f(a, b, c) = ((f a) b) c:
        // - Argument goes to c
        // - Function, Argument goes to b
        // - Function, Function, Argument goes to a
        // - Function, Function, Function goes to f
        //
        // We want to enumerate all subterms, so we recursively process:
        // 1. The function part (if this is an application)
        // 2. The argument part (if this is an application)
        // 3. This term itself

        if let Some((func, arg)) = self.as_ref().split_application() {
            // Process function part
            prefix.push(PathStep::Function);
            func.to_owned()
                .push_rewritable_subterms_with_paths(prefix, answer);
            prefix.pop();

            // Process argument part
            prefix.push(PathStep::Argument);
            arg.to_owned()
                .push_rewritable_subterms_with_paths(prefix, answer);
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
    end: usize,
}

impl<'a> Iterator for TermRefArgsIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position >= self.end {
            return None;
        }

        match self.components[self.position] {
            TermComponent::Application { span } => {
                // Composite argument - return the whole Application-wrapped term
                let arg_end = self.position + span as usize;
                if arg_end > self.end {
                    panic!(
                        "iter_args: span {} at position {} exceeds end {}. Components: {:?}",
                        span, self.position, self.end, self.components
                    );
                }
                let arg_slice = &self.components[self.position..arg_end];
                self.position = arg_end;
                Some(TermRef::new(arg_slice))
            }
            TermComponent::Atom(_) => {
                // Simple atomic argument as a single-element slice
                let arg_slice = &self.components[self.position..self.position + 1];
                self.position += 1;
                Some(TermRef::new(arg_slice))
            }
            TermComponent::Pi { .. } => {
                panic!("Pi should not appear in open terms");
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
        // compound term incorrectly wrapped the result in a Application marker.
        //
        // Term: x0(x1) - variable x0 applied to x1
        // Replace x0 with m0(c0) - a compound term
        // Expected result: m0(c0, x1) - m0 applied to c0 and x1
        // Bug would produce: [Application, m0, c0, x1] which is invalid
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
        // Non-head position should still wrap in Application
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

    #[test]
    fn test_new_term_format() {
        // Test that non-atomic terms start with Application
        let term = Term::parse("c0(c1)");
        assert!(
            matches!(term.components()[0], TermComponent::Application { .. }),
            "Non-atomic term should start with Application. Got: {:?}",
            term.components()
        );

        // Test atomic term does NOT start with Application
        let atomic = Term::parse("c0");
        assert!(
            matches!(atomic.components()[0], TermComponent::Atom(_)),
            "Atomic term should start with Atom"
        );

        // Test nested term
        let nested = Term::parse("c0(c1(c2), c3)");
        assert!(
            matches!(nested.components()[0], TermComponent::Application { .. }),
            "Nested term should start with Application"
        );
        assert_eq!(nested.num_args(), 2);

        // Test decompose on new format
        let term2 = Term::parse("c0(c1, c2)");
        if let Decomposition::Application(func, arg) = term2.as_ref().decompose() {
            assert_eq!(format!("{}", func), "c0(c1)");
            assert_eq!(format!("{}", arg), "c2");
        } else {
            panic!("Expected Application decomposition");
        }
    }
}
