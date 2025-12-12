use serde::{Deserialize, Serialize};
use std::fmt;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::types::GroundTypeId;

/// A step in a path through a term.
/// Treats applications in curried form: f(a, b) becomes ((f a) b).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PathStep {
    /// Go to the function part of an application
    Function,
    /// Go to the argument part of an application
    Argument,
}

/// A component of a Term in its flattened representation.
/// This is private to the term module - external code should use decomposition methods.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Serialize, Deserialize)]
enum TermComponent {
    /// Indicates a function application with the given span (total number of components).
    /// The span includes this Application marker itself, the head, and all arguments recursively.
    /// To skip over this entire subterm: index += span
    /// To enter this subterm (process the head): index += 1
    /// Used in Term (open terms with free variables).
    Application { span: u16 },

    /// A Pi type (dependent function type) with the given span.
    /// The span includes this Pi marker, the binder type, and the body.
    /// Pi always has exactly 2 sub-elements: binder type and body.
    /// Used when Term represents types like `(T : Type<CommRing>) -> T -> T -> T`.
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

    /// A Pi type (dependent function type): (x : input) -> output.
    /// For non-dependent arrow types, output doesn't reference the bound variable.
    /// Both input and output are borrowed slices - no allocation.
    Pi(TermRef<'a>, TermRef<'a>),
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
    fn new(components: &'a [TermComponent]) -> TermRef<'a> {
        TermRef { components }
    }

    /// Convert this borrowed TermRef to an owned Term.
    pub fn to_owned(&self) -> Term {
        if self.components.is_empty() {
            panic!("Cannot convert empty TermRef to Term");
        }

        // Verify format is correct
        if self.components.len() > 1 {
            match self.components[0] {
                TermComponent::Application { span } | TermComponent::Pi { span } => {
                    debug_assert_eq!(
                        span as usize,
                        self.components.len(),
                        "to_owned: span {} doesn't match len {}",
                        span,
                        self.components.len()
                    );
                }
                _ => panic!(
                    "to_owned: non-atomic term should start with Application or Pi, got: {:?}",
                    self.components
                ),
            }
        }

        Term {
            components: self.components.to_vec(),
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
                TermComponent::Pi { .. } => {
                    // For Pi types, the head atom is the input type's head atom
                    pos += 1;
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
    /// - `Decomposition::Pi(input, output)` if the term is a Pi type
    ///
    /// All returned references are borrowed slices - no allocation needed.
    /// This provides a cleaner way to write recursive algorithms on terms
    /// by pattern matching on the structure rather than checking multiple conditions.
    pub fn decompose(&self) -> Decomposition<'a> {
        // Handle atomic terms (single Atom, no Application/Pi wrapper)
        if self.components.len() == 1 {
            let atom = match &self.components[0] {
                TermComponent::Atom(atom) => atom,
                _ => panic!("atomic term should have Atom component"),
            };
            return Decomposition::Atom(atom);
        }

        // Non-atomic terms start with Application or Pi
        match self.components[0] {
            TermComponent::Application { span: outer_span } => {
                // Position 1 is where func starts
                let func_end = self.find_subterm_end(1);
                let func = TermRef::new(&self.components[1..func_end]);

                // arg starts right after func
                let arg_start = func_end;
                let arg_end = outer_span as usize;
                let arg = TermRef::new(&self.components[arg_start..arg_end]);

                Decomposition::Application(func, arg)
            }
            TermComponent::Pi { span: outer_span } => {
                // Pi structure: [Pi{span}, input_type..., output_type...]
                let input_end = self.find_subterm_end(1);
                let input = TermRef::new(&self.components[1..input_end]);

                let output_start = input_end;
                let output_end = outer_span as usize;
                let output = TermRef::new(&self.components[output_start..output_end]);

                Decomposition::Pi(input, output)
            }
            TermComponent::Atom(_) => panic!(
                "non-atomic term should start with Application or Pi, got: {:?}",
                self.components
            ),
        }
    }

    /// Find the end position of a subterm starting at `start`.
    fn find_subterm_end(&self, start: usize) -> usize {
        match self.components[start] {
            TermComponent::Pi { span } | TermComponent::Application { span } => {
                start + span as usize
            }
            TermComponent::Atom(_) => start + 1,
        }
    }

    /// Split an application into (function, argument) in curried form.
    /// For f(a, b, c), returns (f(a, b), c).
    /// Returns None if the term is atomic or a Pi type.
    ///
    /// Both returned TermRefs are slices of the original - no allocation needed.
    pub fn split_application(&self) -> Option<(TermRef<'a>, TermRef<'a>)> {
        match self.decompose() {
            Decomposition::Application(func, arg) => Some((func, arg)),
            _ => None,
        }
    }

    /// Check if this term is a Pi type (dependent function type).
    pub fn is_pi(&self) -> bool {
        matches!(self.components.first(), Some(TermComponent::Pi { .. }))
    }

    /// Split a Pi type into (input_type, output_type).
    /// Returns None if the term is not a Pi type.
    ///
    /// Both returned TermRefs are slices of the original - no allocation needed.
    pub fn split_pi(&self) -> Option<(TermRef<'a>, TermRef<'a>)> {
        match self.decompose() {
            Decomposition::Pi(input, output) => Some((input, output)),
            _ => None,
        }
    }

    /// Check if this term starts with an Application marker.
    /// This is different from has_args() which checks for any application structure.
    /// is_application() specifically checks for the top-level Application{span} marker.
    pub fn is_application(&self) -> bool {
        matches!(
            self.components.first(),
            Some(TermComponent::Application { .. })
        )
    }

    /// Split a type application into (head, args).
    /// Returns None if the term doesn't start with an Application marker.
    /// Unlike split_application() which returns (func, last_arg) for curried apps,
    /// this returns the head and ALL arguments as owned Terms.
    pub fn split_application_multi(&self) -> Option<(Term, Vec<Term>)> {
        match self.components.first() {
            Some(TermComponent::Application { span }) => {
                let total_span = *span as usize;
                // Find where the head ends
                let head_end = self.find_subterm_end(1);
                let head = TermRef::new(&self.components[1..head_end]).to_owned();

                // Collect all arguments
                let mut args = Vec::new();
                let mut pos = head_end;
                while pos < total_span {
                    let arg_end = self.find_subterm_end(pos);
                    let arg = TermRef::new(&self.components[pos..arg_end]).to_owned();
                    args.push(arg);
                    pos = arg_end;
                }

                Some((head, args))
            }
            _ => None,
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

    /// If this is an atomic Type symbol, return its GroundTypeId.
    /// This is used for ground types when Term represents a type.
    pub fn as_type_atom(&self) -> Option<GroundTypeId> {
        if !self.is_atomic() {
            return None;
        }
        match self.get_head_atom() {
            Atom::Symbol(Symbol::Type(t)) => Some(*t),
            _ => None,
        }
    }

    /// Get the term's type as a Term with context.
    /// Uses LocalContext for variable types and KernelContext for symbol types.
    /// For function applications, recursively gets the function's type and applies it.
    pub fn get_type_with_context(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Term {
        match self.decompose() {
            Decomposition::Atom(atom) => match atom {
                Atom::Variable(i) => local_context
                    .get_var_type(*i as usize)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "Variable x{} not found in LocalContext (size={}). TermRef components: {:?}",
                            i,
                            local_context.len(),
                            self.components
                        )
                    }),
                Atom::Symbol(symbol) => kernel_context.symbol_table.get_type(*symbol).clone(),
            },
            Decomposition::Application(func, _arg) => {
                // The function has type A -> B, so the application has type B
                let func_type = func.get_type_with_context(local_context, kernel_context);
                func_type
                    .type_apply()
                    .expect("Function type expected but not found during type application")
            }
            Decomposition::Pi(_, _) => {
                // Pi types are themselves types - this is used when the term IS a type
                // Return the type of types (Empty) for now
                Term::type_empty()
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
        // A term has args if it starts with Application (non-atomic terms always start with Application)
        matches!(self.components[0], TermComponent::Application { .. })
    }

    /// Get the number of arguments this term has.
    pub fn num_args(&self) -> usize {
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
        // For nested format [Application{5}, Application{3}, f, a, b]:
        // Collect args by walking the nested applications via split_application.
        // This collects innermost first, so we reverse at the end.

        if self.is_atomic() {
            return TermRefArgsIterator {
                components: self.components,
                arg_positions: Vec::new(),
                current_index: 0,
            };
        }

        let mut arg_positions = Vec::new();
        let mut current = *self;

        while !current.is_atomic() {
            match current.split_application() {
                Some((func, arg)) => {
                    // Record arg bounds relative to original term
                    let arg_offset =
                        arg.components.as_ptr() as usize - self.components.as_ptr() as usize;
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
                    // Pi types contribute to weight like Application
                    weight1 += 1;
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
                TermComponent::Atom(Atom::Symbol(Symbol::Type(t))) => {
                    // Type atoms contribute to weight
                    weight1 += 1;
                    weight2 += 4 * t.as_u16() as u32;
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
            // Non-atomic term: format the contents (skip the Application marker)
            let end = pos + *span as usize;
            format_application_contents(f, components, pos + 1, end)
        }
        TermComponent::Atom(atom) => {
            // Atomic term - just format the atom
            match atom {
                Atom::Variable(i) => write!(f, "x{}", i)?,
                _ => write!(f, "{}", atom)?,
            }
            Ok(())
        }
        TermComponent::Pi { span } => {
            // Pi type: format as (input -> output)
            let end = pos + *span as usize;
            format_pi_contents(f, components, pos + 1, end)
        }
    }
}

/// Format the contents of an application (func + arg) from start to end.
/// Terms use nested Application markers:
///   - f(a, b): [App{5}, App{3}, f, a, b] - func is another App, arg is last
///   - f(g(x)): [App{4}, f, App{3}, g, x] - func is atomic, arg is compound
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

/// Format the contents of a Pi type (input -> output) from start to end.
fn format_pi_contents(
    f: &mut fmt::Formatter,
    components: &[TermComponent],
    start: usize,
    end: usize,
) -> fmt::Result {
    if start >= end {
        return Ok(());
    }

    // Find where the input type ends
    let input_end = find_subterm_end_at(components, start);
    let output_start = input_end;

    write!(f, "(")?;
    format_term_slice(f, components, start, input_end)?;
    write!(f, " -> ")?;
    format_term_slice(f, components, output_start, end)?;
    write!(f, ")")
}

/// Find the end position of a subterm starting at `start` in a components slice.
fn find_subterm_end_at(components: &[TermComponent], start: usize) -> usize {
    match components[start] {
        TermComponent::Pi { span } | TermComponent::Application { span } => start + span as usize,
        TermComponent::Atom(_) => start + 1,
    }
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
        TermComponent::Pi { span } => {
            let actual_end = start + *span as usize;
            debug_assert_eq!(actual_end, end, "span mismatch in format_term_slice for Pi");
            format_pi_contents(f, components, start + 1, end)
        }
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
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Serialize, Deserialize)]
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
                // Non-atomic func - must be wrapped in Application
                match func_components[0] {
                    TermComponent::Application { span } => {
                        debug_assert_eq!(
                            span as usize, func_len,
                            "Term::new: func has Application with wrong span"
                        );
                        new_components.extend(func_components.iter().copied());
                    }
                    _ => panic!(
                        "Term::new: non-atomic func should start with Application: {:?}",
                        func_components
                    ),
                }
            }

            // Add the argument
            if arg_len == 1 {
                // Atomic argument
                new_components.push(arg.components[0]);
            } else {
                // Compound argument - must have Application wrapper
                match arg.components[0] {
                    TermComponent::Application { span } => {
                        debug_assert_eq!(
                            span as usize, arg_len,
                            "Term::new: arg {} has Application with wrong span {} (expected {})",
                            i, span, arg_len
                        );
                        new_components.extend(arg.components.iter().copied());
                    }
                    _ => panic!(
                        "Term::new: non-atomic arg {} should start with Application: {:?}",
                        i, arg.components
                    ),
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
    /// Atomic terms have a single Atom component.
    /// Non-atomic terms start with an Application or Pi marker containing the span.
    fn from_components(components: Vec<TermComponent>) -> Term {
        if components.is_empty() {
            panic!("from_components: empty components");
        }
        // Basic validation: check first component
        match components[0] {
            TermComponent::Application { span } => {
                // Non-atomic term: position 1 can be Atom, Application, or Pi
                if components.len() < 2 {
                    panic!(
                        "from_components: Application at start but no content. Components: {:?}",
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
            TermComponent::Pi { span } => {
                // Pi type: must have at least input and output
                if components.len() < 3 {
                    panic!(
                        "from_components: Pi at start but not enough content. Components: {:?}",
                        components
                    );
                }
                if span as usize != components.len() {
                    panic!(
                        "from_components: outer Pi span {} doesn't match components length {}. Components: {:?}",
                        span, components.len(), components
                    );
                }
            }
            TermComponent::Atom(_) => {
                // Atomic term (len must be 1)
                if components.len() != 1 {
                    panic!(
                        "from_components: non-atomic term should start with Application or Pi, got: {:?}",
                        components
                    );
                }
            }
        }
        // Debug check to catch bad spans
        #[cfg(debug_assertions)]
        {
            let mut i = 0;
            while i < components.len() {
                match components[i] {
                    TermComponent::Application { span } | TermComponent::Pi { span } => {
                        let end = i + span as usize;
                        if end > components.len() {
                            panic!(
                                "from_components: span at {} is {} but only {} components total. Components: {:?}",
                                i, span, components.len(), components
                            );
                        }
                        i = end;
                    }
                    TermComponent::Atom(_) => {
                        i += 1;
                    }
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

    /// Create a Pi type `(x : input) -> output`.
    /// For non-dependent arrow types, output simply doesn't reference `Atom::Variable(0)`.
    pub fn pi(input: Term, output: Term) -> Term {
        let span = 1 + input.components.len() + output.components.len();
        let mut components = vec![TermComponent::Pi { span: span as u16 }];
        components.extend(input.components);
        components.extend(output.components);
        Term { components }
    }

    /// Create an Application term with a head and multiple arguments.
    /// This creates: [Application{span}, head_components..., arg1_components..., arg2_components..., ...]
    pub fn application_multi(head: Term, args: Vec<Term>) -> Term {
        debug_assert!(
            !args.is_empty(),
            "application_multi requires at least one argument"
        );
        let mut total_len = 1 + head.components.len();
        for arg in &args {
            total_len += arg.components.len();
        }

        let mut components = Vec::with_capacity(total_len);
        components.push(TermComponent::Application {
            span: total_len as u16,
        });
        components.extend(head.components);
        for arg in args {
            components.extend(arg.components);
        }

        Term { components }
    }

    // ========== Type-related methods ==========
    // These methods are for when Term is used to represent a type.

    /// Create a Term representing a ground type.
    pub fn type_ground(type_id: GroundTypeId) -> Term {
        Term::atom(Atom::Symbol(Symbol::Type(type_id)))
    }

    /// Returns a Term for the Bool type.
    pub fn type_bool() -> Term {
        Term::type_ground(GroundTypeId::new(1))
    }

    /// Returns a static reference to the Bool type.
    pub fn type_bool_ref() -> &'static Term {
        use std::sync::LazyLock;
        static BOOL_TYPE: LazyLock<Term> = LazyLock::new(Term::type_bool);
        &BOOL_TYPE
    }

    /// Returns a Term for the Empty type.
    pub fn type_empty() -> Term {
        Term::type_ground(GroundTypeId::new(0))
    }

    /// Returns a static reference to the Empty type.
    pub fn type_empty_ref() -> &'static Term {
        use std::sync::LazyLock;
        static EMPTY_TYPE: LazyLock<Term> = LazyLock::new(Term::type_empty);
        &EMPTY_TYPE
    }

    /// Create a type application like `List[Int]` or `Map[String, Int]`.
    /// `head` is the type constructor, `args` are the type parameters.
    pub fn type_application(head: Term, args: Vec<Term>) -> Term {
        debug_assert!(
            !args.is_empty(),
            "type_application requires at least one argument"
        );
        Term::application_multi(head, args)
    }

    /// Apply a function type to get its codomain.
    /// Returns None if this is not a Pi type.
    pub fn type_apply(&self) -> Option<Term> {
        self.as_ref()
            .split_pi()
            .map(|(_, output)| output.to_owned())
    }

    /// Validates that all spans in this term are correct.
    /// Returns true if valid, false otherwise.
    /// This is primarily for debug assertions.
    #[cfg(debug_assertions)]
    pub fn validate_structure(&self) -> bool {
        // Check that the first component has correct span if non-atomic
        if self.components.len() > 1 {
            match self.components[0] {
                TermComponent::Application { span } | TermComponent::Pi { span } => {
                    if span as usize != self.components.len() {
                        return false;
                    }
                }
                TermComponent::Atom(_) => return false, // Non-atomic must start with marker
            }
        }
        // Check all internal spans
        let mut i = 0;
        while i < self.components.len() {
            match self.components[i] {
                TermComponent::Application { span } | TermComponent::Pi { span } => {
                    let end = i + span as usize;
                    if end > self.components.len() {
                        return false;
                    }
                    i += 1; // Move to first element inside the span
                }
                TermComponent::Atom(_) => {
                    i += 1;
                }
            }
        }
        true
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
    /// Used in tests and debug assertions.
    #[cfg(test)]
    fn components(&self) -> &[TermComponent] {
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
                TermComponent::Pi { .. } => {
                    // For Pi types, the head atom is the input type's head atom
                    pos += 1;
                }
            }
        }
    }

    /// Get the term's type as a Term with context.
    /// Uses LocalContext for variable types and KernelContext for symbol types.
    /// For function applications, applies the function type once per argument.
    pub fn get_type_with_context(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Term {
        self.as_ref()
            .get_type_with_context(local_context, kernel_context)
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
    /// Returns (AtomId, Term) pairs for each variable found (where Term is the variable's type).
    /// Uses the local_context to look up variable types.
    pub fn collect_vars(&self, local_context: &LocalContext) -> Vec<(AtomId, Term)> {
        let mut result = Vec::new();
        for atom in self.iter_atoms() {
            if let Atom::Variable(id) = atom {
                let var_type = local_context
                    .get_var_type(*id as usize)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "Variable x{} not found in local context (context has {} types). Term: {}",
                            id,
                            local_context.len(),
                            self
                        )
                    });
                result.push((*id, var_type));
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
            Decomposition::Pi(input_ref, output_ref) => {
                // Recursively replace in both input and output types
                let input = input_ref.to_owned();
                let output = output_ref.to_owned();

                let new_input = input.replace_variable_impl(id, value);
                let new_output = output.replace_variable_impl(id, value);

                // Rebuild the Pi type
                Term::pi(new_input, new_output)
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

        // Test decompose
        let term2 = Term::parse("c0(c1, c2)");
        if let Decomposition::Application(func, arg) = term2.as_ref().decompose() {
            assert_eq!(format!("{}", func), "c0(c1)");
            assert_eq!(format!("{}", arg), "c2");
        } else {
            panic!("Expected Application decomposition");
        }
    }
}
