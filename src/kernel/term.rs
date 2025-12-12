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
    /// Both func and arg are borrowed slices from the original term - no allocation.
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
    /// Always produces new-format Terms (with Application wrapper for non-atomic terms).
    pub fn to_owned(&self) -> Term {
        if self.components.is_empty() {
            panic!("Cannot convert empty TermRef to Term");
        }

        // If atomic or already new format, just copy
        if self.components.len() == 1 {
            return Term {
                components: self.components.to_vec(),
            };
        }

        match self.components[0] {
            TermComponent::Application { span } => {
                // Already new format - verify span is correct
                debug_assert_eq!(
                    span as usize,
                    self.components.len(),
                    "to_owned: Application span {} doesn't match len {}",
                    span,
                    self.components.len()
                );
                Term {
                    components: self.components.to_vec(),
                }
            }
            TermComponent::Atom(_) => {
                // Old format - wrap in Application
                let mut components = Vec::with_capacity(self.components.len() + 1);
                components.push(TermComponent::Application {
                    span: (self.components.len() + 1) as u16,
                });
                components.extend(self.components.iter().copied());
                Term { components }
            }
            TermComponent::Pi { .. } => {
                panic!("to_owned: Term should not start with Pi");
            }
        }
    }

    /// Get the head atom of this term.
    /// The head is always the first component (or first after Application marker).
    pub fn get_head_atom(&self) -> &Atom {
        // Find the head atom by skipping through nested Application markers
        let mut pos = 0;
        loop {
            match &self.components[pos] {
                TermComponent::Atom(atom) => return atom,
                TermComponent::Application { .. } => {
                    // Skip to the func part (position after the Application marker)
                    pos += 1;
                }
                TermComponent::Pi { span } => {
                    panic!(
                        "Term should not start with Pi marker. Components: {:?}, span: {}",
                        self.components, span
                    )
                }
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
    /// The func is an owned Term (always in new format), arg is a borrowed slice.
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

        // Check if this is new format (nested applications) or old format
        match self.components[0] {
            TermComponent::Application { span: outer_span } => {
                // New format: [Application{outer}, func_part..., arg_part...]
                // Position 1 is where func starts
                let func_end = match self.components[1] {
                    TermComponent::Application { span } => 1 + span as usize,
                    TermComponent::Atom(_) => 2, // func is atomic, so just 1 atom at position 1
                    TermComponent::Pi { .. } => panic!("Pi in term"),
                };

                let func = TermRef::new(&self.components[1..func_end]);

                // arg starts right after func
                let arg_start = func_end;
                let arg_end = outer_span as usize;
                let arg = TermRef::new(&self.components[arg_start..arg_end]);

                Decomposition::Application(func, arg)
            }
            TermComponent::Atom(_) => {
                // Old format: [head, arg1, arg2, ...]
                // Find the start of the last argument
                let mut prev_position = 1;
                let mut position = 1;

                while position < self.components.len() {
                    prev_position = position;
                    match self.components[position] {
                        TermComponent::Application { span } => {
                            position += span as usize;
                        }
                        TermComponent::Atom(_) => {
                            position += 1;
                        }
                        TermComponent::Pi { .. } => {
                            panic!("Pi in term");
                        }
                    }
                }

                // Build func_part - this still needs allocation for old format
                let func_term = if prev_position == 1 {
                    // Only one argument - func_part is just the head atom
                    Term {
                        components: vec![self.components[0]],
                    }
                } else {
                    // Multiple arguments - need to build [Application{span}, head, args_except_last]
                    let mut components = Vec::with_capacity(1 + prev_position);
                    components.push(TermComponent::Application { span: 0 }); // Placeholder
                    components.extend(self.components[0..prev_position].iter().copied());
                    components[0] = TermComponent::Application {
                        span: components.len() as u16,
                    };
                    Term { components }
                };

                // Extract the last argument
                let last_arg = match self.components[prev_position] {
                    TermComponent::Application { span } => {
                        let end = prev_position + span as usize;
                        TermRef::new(&self.components[prev_position..end])
                    }
                    TermComponent::Atom(_) => {
                        TermRef::new(&self.components[prev_position..prev_position + 1])
                    }
                    TermComponent::Pi { .. } => panic!("Pi in term"),
                };

                // For old format, we need to return owned Term, but Decomposition uses TermRef.
                // This is a problem - old format can't return zero-copy func.
                // Let's leak the allocation for now (or panic to force new format usage)
                let func_ref = func_term.components.leak();
                Decomposition::Application(TermRef::new(func_ref), last_arg)
            }
            TermComponent::Pi { .. } => panic!("Pi should not appear in term structure"),
        }
    }

    /// Split an application into (function, argument) in curried form.
    /// For f(a, b, c), returns (f(a, b), c).
    /// Returns None if the term is atomic (has no arguments).
    ///
    /// Both returned TermRefs are slices of the original - no allocation needed.
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
        // Use decomposition to count args - this handles both old and new format
        let mut count = 0;
        let mut current = *self;
        while !current.is_atomic() {
            count += 1;
            match current.split_application() {
                Some((func, _arg)) => current = func,
                None => break,
            }
        }
        count
    }

    /// Iterate over the arguments of this term without allocating.
    /// Each argument is returned as a TermRef.
    /// For f(a, b), this yields [a, b] in order.
    pub fn iter_args(&self) -> TermRefArgsIterator<'a> {
        // With the new nested format, we need to collect args by repeated decomposition.
        // But for efficiency, we use a different approach: identify args directly.
        //
        // For new format: [Application{5}, Application{3}, f, a, b]
        //   - Args are collected by walking the func structure
        //   - The last position before func ends is the first arg, etc.
        //
        // For old format: [f, a, b]
        //   - Args are simply positions 1 onwards

        match self.components[0] {
            TermComponent::Application { span: _ } => {
                // New format - collect arg positions by walking nested applications
                let mut arg_positions = Vec::new();
                let mut current = *self;

                while !current.is_atomic() {
                    match current.split_application() {
                        Some((func, arg)) => {
                            // Record arg bounds
                            let arg_offset = arg.components.as_ptr() as usize
                                - self.components.as_ptr() as usize;
                            let arg_start = arg_offset / std::mem::size_of::<TermComponent>();
                            arg_positions.push((arg_start, arg_start + arg.components.len()));
                            current = func;
                        }
                        None => break,
                    }
                }

                // Reverse since we collected innermost first
                arg_positions.reverse();

                TermRefArgsIterator {
                    components: self.components,
                    arg_positions,
                    current_index: 0,
                }
            }
            TermComponent::Atom(_) => {
                if self.components.len() <= 1 {
                    return TermRefArgsIterator {
                        components: self.components,
                        arg_positions: Vec::new(),
                        current_index: 0,
                    };
                }
                // Old format - collect arg positions linearly
                let mut arg_positions = Vec::new();
                let mut pos = 1;
                while pos < self.components.len() {
                    let (start, end) = match self.components[pos] {
                        TermComponent::Application { span } => (pos, pos + span as usize),
                        TermComponent::Atom(_) => (pos, pos + 1),
                        TermComponent::Pi { .. } => panic!("Pi in term"),
                    };
                    arg_positions.push((start, end));
                    pos = end;
                }
                TermRefArgsIterator {
                    components: self.components,
                    arg_positions,
                    current_index: 0,
                }
            }
            TermComponent::Pi { .. } => panic!("Pi should not appear in Term"),
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

/// Format an argument at the given position (old format support).
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
            format_term_slice(f, components, pos, end)?;
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

/// Format the contents of an application (func + arg) from start to end.
/// In the nested format:
///   - For f(a, b): [App{5}, App{3}, f, a, b] - func is another App, arg is last
///   - For f(g(x)): [App{4}, f, App{3}, g, x] - func is atomic, arg is compound
/// We collect all args by walking the curried structure.
fn format_application_contents(
    f: &mut fmt::Formatter,
    components: &[TermComponent],
    start: usize,
    end: usize,
) -> fmt::Result {
    if start >= end {
        return Ok(());
    }

    // Collect all arguments by walking down the curried structure
    let mut args: Vec<(usize, usize)> = Vec::new(); // (start, end) of each arg
    let mut current_start = start;
    let mut current_end = end;

    // Walk down through the structure to find the head and collect args
    loop {
        match &components[current_start] {
            TermComponent::Atom(atom) => {
                // Found the head atom - write it
                match atom {
                    Atom::Variable(i) => write!(f, "x{}", i)?,
                    _ => write!(f, "{}", atom)?,
                }
                // If there's anything after this atom (within our bounds), it's an argument
                let arg_start = current_start + 1;
                if arg_start < current_end {
                    // Collect the remaining content as an argument
                    // For atomic head with compound arg: [head, App{n}, ...]
                    // We need to find where the arg ends
                    match components[arg_start] {
                        TermComponent::Application { span } => {
                            let arg_end = arg_start + span as usize;
                            args.push((arg_start, arg_end));
                            // If there's more after this arg, it's weird (shouldn't happen)
                            // but we'll just stop here
                        }
                        TermComponent::Atom(_) => {
                            // Atomic arg
                            args.push((arg_start, arg_start + 1));
                        }
                        TermComponent::Pi { .. } => return Err(fmt::Error),
                    }
                }
                break;
            }
            TermComponent::Application { span } => {
                // This is a nested application within our current bounds
                // We're looking at an App marker, but the arg comes from current_end, not app_end
                //
                // Example: format_application_contents(f, components, 1, 5) for [App{5}, App{3}, c0, c1, c2]
                // - current_start=1 is App{3} (the func)
                // - current_end=5
                // - The func spans positions 1-4 (span=3)
                // - The arg spans positions 4-5 (= func_end to current_end)

                let func_span = *span as usize;
                let func_end = current_start + func_span;

                // The arg is everything from func_end to current_end
                let arg_start = func_end;
                let arg_end = current_end;

                if arg_start < arg_end {
                    // Add this arg to our list (collecting from outermost to innermost)
                    args.push((arg_start, arg_end));
                }

                // Continue with the func part - go inside the App marker's contents
                let inner_func_start = current_start + 1;
                let inner_func_end = match &components[inner_func_start] {
                    TermComponent::Application { span } => inner_func_start + *span as usize,
                    TermComponent::Atom(_) => inner_func_start + 1,
                    TermComponent::Pi { .. } => return Err(fmt::Error),
                };

                // Check if there's an inner arg (within this nested App)
                let inner_arg_start = inner_func_end;
                let inner_arg_end = func_end; // end of this App's span

                if inner_arg_start < inner_arg_end {
                    // There's an arg inside this nested application
                    args.push((inner_arg_start, inner_arg_end));
                }

                // Continue with inner func
                current_start = inner_func_start;
                current_end = inner_func_end;
            }
            TermComponent::Pi { .. } => {
                return Err(fmt::Error);
            }
        }
    }

    // Now write all the arguments in order
    if !args.is_empty() {
        write!(f, "(")?;
        // args are in reverse order (outermost first collected), so reverse them
        for (i, (arg_start, arg_end)) in args.iter().rev().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            format_term_slice(f, components, *arg_start, *arg_end)?;
        }
        write!(f, ")")?;
    }

    Ok(())
}

/// Format a slice of components as a term.
fn format_term_slice(
    f: &mut fmt::Formatter,
    components: &[TermComponent],
    start: usize,
    end: usize,
) -> fmt::Result {
    if start >= end {
        return Ok(());
    }

    match &components[start] {
        TermComponent::Application { span } => {
            let actual_end = start + *span as usize;
            debug_assert_eq!(actual_end, end, "span mismatch in format_term_slice");
            format_application_contents(f, components, start + 1, end)
        }
        TermComponent::Atom(atom) => {
            match atom {
                Atom::Variable(i) => write!(f, "x{}", i)?,
                _ => write!(f, "{}", atom)?,
            }
            Ok(())
        }
        TermComponent::Pi { .. } => Err(fmt::Error),
    }
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
    /// If args is non-empty, builds nested Application structure for curried form:
    ///   f(a, b) becomes [App{5}, App{3}, f, a, b]
    /// where the inner App{3} represents f(a), and the outer applies that to b.
    pub fn new(head: Atom, args: Vec<Term>) -> Term {
        if args.is_empty() {
            return Term {
                components: vec![TermComponent::Atom(head)],
            };
        }

        // Build nested applications from left to right (curried form)
        // f(a, b, c) = ((f a) b) c
        // Start with the head atom
        let mut func_components: Vec<TermComponent> = vec![TermComponent::Atom(head)];

        for (i, arg) in args.iter().enumerate() {
            if arg.components.is_empty() {
                panic!("Term::new: arg {} is empty", i);
            }

            // Calculate sizes
            let func_len = func_components.len();
            let arg_len = arg.components.len();

            // Build new application: [Application{span}, func_components..., arg_components...]
            // But we need to handle the func_components - if it's just an atom, no wrapper needed inside
            // If it already has components > 1, we need to wrap it in Application
            let mut new_components = Vec::with_capacity(1 + func_len + arg_len + 1);

            // Outer Application for the whole thing
            new_components.push(TermComponent::Application { span: 0 }); // Placeholder

            // Add the func part
            if func_len == 1 {
                // Atomic func - just add it directly
                new_components.extend(func_components.iter().copied());
            } else {
                // Non-atomic func - check if already wrapped in Application
                match func_components[0] {
                    TermComponent::Application { span } => {
                        // Already wrapped - just copy as-is
                        debug_assert_eq!(
                            span as usize, func_len,
                            "Term::new: func has Application with wrong span"
                        );
                        new_components.extend(func_components.iter().copied());
                    }
                    TermComponent::Atom(_) => {
                        // Old format (shouldn't happen in normal use, but handle it)
                        // Wrap in Application
                        new_components.push(TermComponent::Application {
                            span: (func_len + 1) as u16,
                        });
                        new_components.extend(func_components.iter().copied());
                    }
                    TermComponent::Pi { .. } => panic!("Pi in term"),
                }
            }

            // Add the argument
            if arg_len == 1 {
                // Atomic argument
                new_components.push(arg.components[0]);
            } else {
                // Compound argument - should already have Application wrapper
                match arg.components[0] {
                    TermComponent::Application { span } => {
                        debug_assert_eq!(
                            span as usize, arg_len,
                            "Term::new: arg {} has Application with wrong span {} (expected {})",
                            i, span, arg_len
                        );
                        new_components.extend(arg.components.iter().copied());
                    }
                    TermComponent::Atom(_) => {
                        // Old format - wrap in Application
                        new_components.push(TermComponent::Application {
                            span: (arg_len + 1) as u16,
                        });
                        new_components.extend(arg.components.iter().copied());
                    }
                    TermComponent::Pi { .. } => {
                        panic!("Term::new: arg {} starts with Pi", i);
                    }
                }
            }

            // Update outer Application span
            new_components[0] = TermComponent::Application {
                span: new_components.len() as u16,
            };

            func_components = new_components;
        }

        Term {
            components: func_components,
        }
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
                // New format: position 1 can be Atom (for simple f(a)) or Application (for nested f(a,b))
                if components.len() < 2 {
                    panic!(
                        "from_components: Application at start but no content. Components: {:?}",
                        components
                    );
                }
                match &components[1] {
                    TermComponent::Atom(_) | TermComponent::Application { .. } => {
                        // Valid: either atomic head or nested application
                    }
                    TermComponent::Pi { .. } => {
                        panic!(
                            "from_components: Application at start followed by Pi. Components: {:?}",
                            components
                        );
                    }
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
        // Find the head atom by skipping through nested Application markers
        let mut pos = 0;
        loop {
            match &self.components[pos] {
                TermComponent::Atom(atom) => return atom,
                TermComponent::Application { .. } => {
                    // Skip to the func part (position after the Application marker)
                    pos += 1;
                }
                TermComponent::Pi { span } => {
                    panic!(
                        "Term should not start with Pi marker. Components: {:?}, span: {}",
                        self.components, span
                    )
                }
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
    arg_positions: Vec<(usize, usize)>, // (start, end) for each arg
    current_index: usize,
}

impl<'a> Iterator for TermRefArgsIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index >= self.arg_positions.len() {
            return None;
        }

        let (start, end) = self.arg_positions[self.current_index];
        self.current_index += 1;
        Some(TermRef::new(&self.components[start..end]))
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
