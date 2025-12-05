use qp_trie::{Entry, SubTrie, Trie};

use crate::kernel::aliases::{Clause, Literal, Term};
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::TermRef;
use crate::kernel::types::TypeId;
/// Replaces variables in a term with corresponding replacement terms.
/// Variables x_i are replaced with replacements[i].
/// If a variable index >= replacements.len() and shift is Some, the variable is shifted.
/// If a variable index >= replacements.len() and shift is None, panics.
///
/// Also builds the output context from:
/// - The replacement_context (for variables in replacements)
/// - The term_context (for shifted variables)
pub fn replace_term_variables(
    term: &Term,
    term_context: &LocalContext,
    replacements: &[TermRef],
    replacement_context: &LocalContext,
    shift: Option<AtomId>,
) -> (Term, LocalContext) {
    let mut output_var_types: Vec<TypeId> = replacement_context.var_types.clone();

    fn replace_recursive(
        term: TermRef,
        term_context: &LocalContext,
        replacements: &[TermRef],
        shift: Option<AtomId>,
        output_var_types: &mut Vec<TypeId>,
    ) -> Term {
        let head = term.get_head_atom();

        if let Atom::Variable(var_id) = head {
            let idx = *var_id as usize;
            if idx < replacements.len() {
                // Replace with the replacement term
                let replacement = replacements[idx];
                if term.has_args() {
                    // f(args) where f is a variable being replaced
                    // Result: replacement applied to args
                    let replacement_term = replacement.to_owned();
                    let replaced_args: Vec<Term> = term
                        .iter_args()
                        .map(|arg| {
                            replace_recursive(
                                arg,
                                term_context,
                                replacements,
                                shift,
                                output_var_types,
                            )
                        })
                        .collect();
                    replacement_term.apply(&replaced_args)
                } else {
                    // Just a variable, return the replacement
                    replacement.to_owned()
                }
            } else {
                // Shift the variable
                let new_var_id = match shift {
                    Some(s) => *var_id + s,
                    None => panic!("no replacement for variable x{}", var_id),
                };
                // Track the type for the shifted variable
                let new_idx = new_var_id as usize;
                let var_type = term_context.get_var_type(idx).unwrap_or(TypeId::default());
                if new_idx >= output_var_types.len() {
                    output_var_types.resize(new_idx + 1, TypeId::default());
                }
                output_var_types[new_idx] = var_type;

                if term.has_args() {
                    let replaced_args: Vec<Term> = term
                        .iter_args()
                        .map(|arg| {
                            replace_recursive(
                                arg,
                                term_context,
                                replacements,
                                shift,
                                output_var_types,
                            )
                        })
                        .collect();
                    Term::new(Atom::Variable(new_var_id), replaced_args)
                } else {
                    Term::atom(Atom::Variable(new_var_id))
                }
            }
        } else {
            // Not a variable head - recurse into args if any
            if term.has_args() {
                let replaced_args: Vec<Term> = term
                    .iter_args()
                    .map(|arg| {
                        replace_recursive(arg, term_context, replacements, shift, output_var_types)
                    })
                    .collect();
                Term::new(*head, replaced_args)
            } else {
                term.to_owned()
            }
        }
    }

    let result_term = replace_recursive(
        term.as_ref(),
        term_context,
        replacements,
        shift,
        &mut output_var_types,
    );
    let result_context = LocalContext::new(output_var_types);
    (result_term, result_context)
}

/// A pattern tree is built from edges.
/// It is a "perfect discrimination tree", designed to store patterns and match them against
/// specialized instances.
///
/// Each path from the root to a leaf is a series of edges.
/// It can represent a term, term pair, or clause.
/// A path starts with "category edges" that differentiate what sort of thing we're matching.
/// Category edges are just matched exactly, no substitutions.
/// After the category edges are the "term edges", which represent the structure of one term
/// or a number of terms, and do allow substitutions. These are "Head" and "Atom" edges.
/// The category edges should indicate how many terms are represented by the term edges.
///
/// Plain terms are encoded as:
///   TermCategory <term>
///
/// Term pairs are encoded as:
///   TermPairCategory <left term> <right term>
///
/// Clauses are encoded with their categories first. For example a = b or not c = d is:
///   PositiveLiteral NegativeLiteral <a> <b> <c> <d>
///   
///
/// HeadType and Atom edges form a preorder traversal of the tree.
/// For any non-atomic term, we include the type of its head, then recurse.
/// For any atom, we just include the atom.
/// This doesn't contain enough type information to extract a term from the tree, but it
/// does contain enough type information to match against an existing term, as long as having
/// an atomic variable at the root level is forbidden.
#[derive(Debug)]
enum Edge {
    /// Number of args, and the type of the head atom.
    Head(u8, TypeId),

    /// Just an atom.
    Atom(Atom),

    /// Category edge to indicate a term of a particular type.
    TermCategory(TypeId),

    /// Category edge, including the type of both left and right of the literal.
    TermPairCategory(TypeId),

    /// Category edge used in clauses, for positive literals.
    PositiveLiteral(TypeId),

    /// Category edge used in clauses, for negative literals.
    NegativeLiteral(TypeId),
}

/// Used for converting Edges into byte sequences.
/// Any byte below MAX_ARGS indicates a composite term with that number of arguments.
const MAX_ARGS: u8 = 100;
const TRUE: u8 = 101;
const GLOBAL_CONSTANT: u8 = 102;
const SCOPED_CONSTANT: u8 = 103;
const MONOMORPH: u8 = 104;
const VARIABLE: u8 = 105;
const SYNTHETIC: u8 = 106;
const TERM: u8 = 107;
const TERM_PAIR: u8 = 108;
const POSITIVE_LITERAL: u8 = 109;
const NEGATIVE_LITERAL: u8 = 110;

impl Edge {
    fn first_byte(&self) -> u8 {
        match self {
            Edge::Head(num_args, _) => *num_args,
            Edge::Atom(a) => match a {
                Atom::True => TRUE,
                Atom::Symbol(Symbol::GlobalConstant(_)) => GLOBAL_CONSTANT,
                Atom::Symbol(Symbol::ScopedConstant(_)) => SCOPED_CONSTANT,
                Atom::Symbol(Symbol::Monomorph(_)) => MONOMORPH,
                Atom::Variable(_) => VARIABLE,
                Atom::Symbol(Symbol::Synthetic(_)) => SYNTHETIC,
            },
            Edge::TermCategory(..) => TERM,
            Edge::TermPairCategory(..) => TERM_PAIR,
            Edge::PositiveLiteral(..) => POSITIVE_LITERAL,
            Edge::NegativeLiteral(..) => NEGATIVE_LITERAL,
        }
    }

    fn append_to(&self, v: &mut Vec<u8>) {
        v.push(self.first_byte());
        let id: u16 = match self {
            Edge::Head(_, t) => t.as_u16(),
            Edge::Atom(a) => match a {
                Atom::True => 0,
                Atom::Symbol(Symbol::GlobalConstant(c)) => *c,
                Atom::Symbol(Symbol::ScopedConstant(c)) => *c,
                Atom::Symbol(Symbol::Monomorph(m)) => *m,
                Atom::Variable(i) => *i,
                Atom::Symbol(Symbol::Synthetic(s)) => *s,
            },
            Edge::TermCategory(t) => t.as_u16(),
            Edge::TermPairCategory(t) => t.as_u16(),
            Edge::PositiveLiteral(t) => t.as_u16(),
            Edge::NegativeLiteral(t) => t.as_u16(),
        };
        v.extend_from_slice(&id.to_ne_bytes());
    }

    fn from_bytes(byte1: u8, byte2: u8, byte3: u8) -> Edge {
        let id = u16::from_ne_bytes([byte2, byte3]);
        match byte1 {
            TRUE => Edge::Atom(Atom::True),
            GLOBAL_CONSTANT => Edge::Atom(Atom::Symbol(Symbol::GlobalConstant(id))),
            SCOPED_CONSTANT => Edge::Atom(Atom::Symbol(Symbol::ScopedConstant(id))),
            MONOMORPH => Edge::Atom(Atom::Symbol(Symbol::Monomorph(id))),
            VARIABLE => Edge::Atom(Atom::Variable(id)),
            SYNTHETIC => Edge::Atom(Atom::Symbol(Symbol::Synthetic(id))),
            TERM_PAIR => Edge::TermPairCategory(TypeId::new(id)),
            POSITIVE_LITERAL => Edge::PositiveLiteral(TypeId::new(id)),
            NEGATIVE_LITERAL => Edge::NegativeLiteral(TypeId::new(id)),
            num_args => {
                if num_args > MAX_ARGS {
                    panic!("invalid discriminant byte");
                }
                Edge::Head(num_args, TypeId::new(id))
            }
        }
    }

    fn debug_bytes(bytes: &[u8]) -> String {
        let mut i = 0;
        let mut parts: Vec<String> = vec![];
        while i < bytes.len() {
            if i + 3 <= bytes.len() {
                let edge = Edge::from_bytes(bytes[i], bytes[i + 1], bytes[i + 2]);
                parts.push(format!("{:?}", edge));
            } else {
                parts.push(format!("plus extra bytes {:?}", &bytes[i..]));
            }
            i += 3;
        }

        parts.join(", ")
    }
}

/// Appends the key for this term, but does not add the top-level type
fn key_from_term_helper(
    term: TermRef,
    key: &mut Vec<u8>,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) {
    if !term.has_args() {
        Edge::Atom(*term.get_head_atom()).append_to(key);
    } else {
        Edge::Head(
            term.num_args() as u8,
            term.get_head_type_with_context(local_context, kernel_context),
        )
        .append_to(key);
        Edge::Atom(*term.get_head_atom()).append_to(key);
        for arg in term.iter_args() {
            key_from_term_helper(arg, key, local_context, kernel_context);
        }
    }
}

pub fn term_key_prefix(type_id: TypeId) -> Vec<u8> {
    let mut key = Vec::new();
    Edge::TermCategory(type_id).append_to(&mut key);
    key
}

/// Appends the key for this term, prefixing with the top-level type
pub fn key_from_term(
    term: &Term,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Vec<u8> {
    let mut key = term_key_prefix(term.get_term_type_with_context(local_context, kernel_context));
    key_from_term_helper(term.as_ref(), &mut key, local_context, kernel_context);
    key
}

fn literal_key_prefix(type_id: TypeId) -> Vec<u8> {
    let mut key = Vec::new();
    Edge::TermPairCategory(type_id).append_to(&mut key);
    key
}

fn key_from_pair(
    term1: &Term,
    term2: &Term,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Vec<u8> {
    let mut key =
        literal_key_prefix(term1.get_term_type_with_context(local_context, kernel_context));
    key_from_term_helper(term1.as_ref(), &mut key, local_context, kernel_context);
    key_from_term_helper(term2.as_ref(), &mut key, local_context, kernel_context);
    key
}

/// Just creates the category prefix for a clause key.
fn clause_key_prefix(clause: &Clause, kernel_context: &KernelContext) -> Vec<u8> {
    let local_context = clause.get_local_context();
    let mut key = Vec::new();
    for literal in &clause.literals {
        if literal.positive {
            Edge::PositiveLiteral(
                literal
                    .left
                    .get_term_type_with_context(local_context, kernel_context),
            )
            .append_to(&mut key);
        } else {
            Edge::NegativeLiteral(
                literal
                    .left
                    .get_term_type_with_context(local_context, kernel_context),
            )
            .append_to(&mut key);
        }
    }
    key
}

/// Generates a key for a clause, starting with the category edges, then the term edges.
fn key_from_clause(clause: &Clause, kernel_context: &KernelContext) -> Vec<u8> {
    let local_context = clause.get_local_context();
    let mut key = clause_key_prefix(clause, kernel_context);
    for literal in &clause.literals {
        key_from_term_helper(
            literal.left.as_ref(),
            &mut key,
            local_context,
            kernel_context,
        );
        key_from_term_helper(
            literal.right.as_ref(),
            &mut key,
            local_context,
            kernel_context,
        );
    }
    key
}

/// Matching implementation using TermRef directly instead of flattened components.
/// Matches a sequence of terms against patterns in the trie.
///
/// This version passes contexts through so types can be computed on-the-fly,
/// avoiding the need for a separate TermComponent type with embedded type info.
fn find_term_matches_while<'a, F>(
    subtrie: &SubTrie<Vec<u8>, usize>,
    key: &mut Vec<u8>,
    terms: &[TermRef<'a>],
    local_context: &LocalContext,
    kernel_context: &KernelContext,
    stack_limit: usize,
    replacements: &mut Vec<TermRef<'a>>,
    callback: &mut F,
) -> bool
where
    F: FnMut(usize, &Vec<TermRef<'a>>) -> bool,
{
    if subtrie.is_empty() {
        return true;
    }

    if stack_limit == 0 {
        return false;
    }

    if terms.is_empty() {
        match subtrie.get(key as &[u8]) {
            Some(value_id) => {
                return callback(*value_id, replacements);
            }
            None => {
                let (sample, _) = subtrie.iter().next().unwrap();
                panic!(
                    "\nkey mismatch.\nquerying: {}\nexisting: {}\n",
                    Edge::debug_bytes(key),
                    Edge::debug_bytes(sample)
                );
            }
        }
    }

    let initial_key_len = key.len();
    let first = terms[0];
    let rest = &terms[1..];

    // Case 1: the first term could match an existing replacement (backreference)
    for i in 0..replacements.len() {
        if first == replacements[i] {
            Edge::Atom(Atom::Variable(i as u16)).append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);
            if !find_term_matches_while(
                &new_subtrie,
                key,
                rest,
                local_context,
                kernel_context,
                stack_limit - 1,
                replacements,
                callback,
            ) {
                return false;
            }
            key.truncate(initial_key_len);
        }
    }

    // Case 2: the first term could match an entirely new variable
    Edge::Atom(Atom::Variable(replacements.len() as u16)).append_to(key);
    let new_subtrie = subtrie.subtrie(key as &[u8]);
    if !new_subtrie.is_empty() {
        replacements.push(first);
        if !find_term_matches_while(
            &new_subtrie,
            key,
            rest,
            local_context,
            kernel_context,
            stack_limit - 1,
            replacements,
            callback,
        ) {
            return false;
        }
        replacements.pop();
    }
    key.truncate(initial_key_len);

    // Case 3: exact match - match the head and then recurse into args + rest
    let head_atom = first.get_head_atom();
    if head_atom.is_variable() {
        // Variables in the query term must match via Cases 1 or 2, not exact match
        return true;
    }

    if first.has_args() {
        // Composite term: match Head edge, then head atom, then args + rest
        let edge = Edge::Head(
            first.num_args() as u8,
            first.get_head_type_with_context(local_context, kernel_context),
        );
        edge.append_to(key);
        let new_subtrie = subtrie.subtrie(key as &[u8]);

        // Now match the head atom
        Edge::Atom(*head_atom).append_to(key);
        let new_subtrie2 = new_subtrie.subtrie(key as &[u8]);

        // Build args + rest as the new sequence to match
        let args: Vec<TermRef<'a>> = first.iter_args().collect();
        let mut next_terms: Vec<TermRef<'a>> = args;
        next_terms.extend_from_slice(rest);

        if !find_term_matches_while(
            &new_subtrie2,
            key,
            &next_terms,
            local_context,
            kernel_context,
            stack_limit - 1,
            replacements,
            callback,
        ) {
            return false;
        }
    } else {
        // Atomic term: just match the atom edge
        Edge::Atom(*head_atom).append_to(key);
        let new_subtrie = subtrie.subtrie(key as &[u8]);
        if !find_term_matches_while(
            &new_subtrie,
            key,
            rest,
            local_context,
            kernel_context,
            stack_limit - 1,
            replacements,
            callback,
        ) {
            return false;
        }
    }

    key.truncate(initial_key_len);
    true
}

#[derive(Clone, Debug)]
pub struct PatternTree<T> {
    /// Maps to an index into values.
    /// The values are stored separately because subtrie lifetimes get weird.
    trie: Trie<Vec<u8>, usize>,

    pub values: Vec<T>,
}

impl<T> PatternTree<T> {
    pub fn new() -> PatternTree<T> {
        PatternTree {
            trie: Trie::new(),
            values: vec![],
        }
    }

    pub fn insert_term(
        &mut self,
        term: &Term,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        let path = key_from_term(term, local_context, kernel_context);
        let value_id = self.values.len();
        self.values.push(value);
        self.trie.insert(path, value_id);
    }

    /// The pair needs to have normalized variable numbering, with term1's variables preceding term2's.
    pub fn insert_pair(
        &mut self,
        term1: &Term,
        term2: &Term,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        let key = key_from_pair(term1, term2, local_context, kernel_context);
        let value_id = self.values.len();
        self.values.push(value);
        self.trie.insert(key, value_id);
    }

    pub fn insert_clause(&mut self, clause: &Clause, value: T, kernel_context: &KernelContext) {
        let key = key_from_clause(clause, kernel_context);
        let value_id = self.values.len();
        self.values.push(value);
        self.trie.insert(key, value_id);
    }

    /// Finds matches using TermRef directly.
    /// Takes a slice of terms to match (for multi-term patterns like pairs/clauses).
    pub fn find_term_matches_while<'a, F>(
        &self,
        key: &mut Vec<u8>,
        terms: &[TermRef<'a>],
        local_context: &LocalContext,
        kernel_context: &KernelContext,
        replacements: &mut Vec<TermRef<'a>>,
        callback: &mut F,
    ) -> bool
    where
        F: FnMut(usize, &Vec<TermRef<'a>>) -> bool,
    {
        let subtrie = self.trie.subtrie(key);
        find_term_matches_while(
            &subtrie,
            key,
            terms,
            local_context,
            kernel_context,
            100,
            replacements,
            callback,
        )
    }

    fn find_pair<'a>(
        &'a self,
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<&'a T> {
        let mut key =
            literal_key_prefix(left.get_term_type_with_context(local_context, kernel_context));
        let terms = [left.as_ref(), right.as_ref()];
        let mut replacements: Vec<TermRef> = vec![];
        let mut found_id = None;
        self.find_term_matches_while(
            &mut key,
            &terms,
            local_context,
            kernel_context,
            &mut replacements,
            &mut |value_id, _| {
                found_id = Some(value_id);
                false // Stop after first match
            },
        );
        found_id.map(|id| &self.values[id])
    }

    pub fn find_clause<'a>(
        &'a self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<&'a T> {
        let local_context = clause.get_local_context();
        let mut key = clause_key_prefix(clause, kernel_context);

        // Build the terms array from all literals in the clause
        let mut terms: Vec<TermRef> = vec![];
        for literal in &clause.literals {
            terms.push(literal.left.as_ref());
            terms.push(literal.right.as_ref());
        }

        let mut replacements: Vec<TermRef> = vec![];
        let mut found_id = None;
        self.find_term_matches_while(
            &mut key,
            &terms,
            local_context,
            kernel_context,
            &mut replacements,
            &mut |value_id, _| {
                found_id = Some(value_id);
                false // Stop after first match
            },
        );
        found_id.map(|id| &self.values[id])
    }
}

impl PatternTree<()> {
    /// Appends to the existing value if possible. Otherwises, inserts a vec![U].
    pub fn insert_or_append<U>(
        pt: &mut PatternTree<Vec<U>>,
        term: &Term,
        value: U,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        let key = key_from_term(term, local_context, kernel_context);
        match pt.trie.entry(key) {
            Entry::Occupied(entry) => {
                let value_id = entry.get();
                pt.values[*value_id].push(value);
            }
            Entry::Vacant(entry) => {
                let value_id = pt.values.len();
                pt.values.push(vec![value]);
                entry.insert(value_id);
            }
        }
    }
}

/// The LiteralSet stores a bunch of literals in a way that makes it quick to check whether
/// the set contains a generalization for a new literal.
#[derive(Clone)]
pub struct LiteralSet {
    /// Stores (sign, id, flipped) for each literal.
    tree: PatternTree<(bool, usize, bool)>,
}

impl LiteralSet {
    pub fn new() -> LiteralSet {
        LiteralSet {
            tree: PatternTree::new(),
        }
    }

    /// Inserts a literal along with its id.
    /// This always inserts the left->right direction.
    /// When the literal is strictly kbo ordered, it can't be reversed and unify with
    /// another literal, so we don't need to insert the right->left direction.
    /// Otherwise, we do insert the right->left direction.
    ///
    /// Overwrites if the negation already exists.
    pub fn insert(
        &mut self,
        literal: &Literal,
        id: usize,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        self.tree.insert_pair(
            &literal.left,
            &literal.right,
            (literal.positive, id, false),
            local_context,
            kernel_context,
        );
        if !literal.strict_kbo() {
            let (right, left, reversed_context) = literal.normalized_reversed(local_context);
            self.tree.insert_pair(
                &right,
                &left,
                (literal.positive, id, true),
                &reversed_context,
                kernel_context,
            );
        }
    }

    /// Checks whether any literal in the tree is a generalization of the provided literal.
    /// If so, returns a pair with:
    ///   1. whether the sign of the generalization matches the literal
    ///   2. the id of the generalization
    ///   3. whether this is a flip-match, meaning we swapped left and right
    pub fn find_generalization(
        &self,
        literal: &Literal,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<(bool, usize, bool)> {
        match self
            .tree
            .find_pair(&literal.left, &literal.right, local_context, kernel_context)
        {
            Some(&(sign, id, flipped)) => Some((sign == literal.positive, id, flipped)),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::types::BOOL;

    /// Creates a test context where all variables have Bool type.
    fn test_local_context(num_vars: usize) -> LocalContext {
        LocalContext::new(vec![BOOL; num_vars])
    }

    #[test]
    fn test_literal_set() {
        let local_context = test_local_context(10);
        // Use Bool types for all symbols - no function application needed for these tests
        let kernel_context =
            KernelContext::test_with_scoped_constant_types(&[BOOL, BOOL, BOOL, BOOL, BOOL]);

        let mut set = LiteralSet::new();
        // Insert "x0 = c0" - a variable equals a constant
        set.insert(
            &Literal::parse("x0 = c0"),
            7,
            &local_context,
            &kernel_context,
        );

        // Exact match
        let lit = Literal::parse("x0 = c0");
        assert!(
            set.find_generalization(&lit, &local_context, &kernel_context)
                .unwrap()
                .0
        );

        // c1 = c0: c1 can be matched by variable x0
        let lit = Literal::parse("c1 = c0");
        assert!(
            set.find_generalization(&lit, &local_context, &kernel_context)
                .unwrap()
                .0
        );

        // x0 = x1: x1 cannot match c0 (c0 is a specific constant)
        let lit = Literal::parse("x0 = x1");
        assert!(set
            .find_generalization(&lit, &local_context, &kernel_context)
            .is_none());

        // Negated version
        let lit = Literal::parse("x0 != c0");
        assert!(
            !set.find_generalization(&lit, &local_context, &kernel_context)
                .unwrap()
                .0
        );

        // Insert "x0 = x0" - a reflexive equality
        set.insert(
            &Literal::parse("x0 = x0"),
            8,
            &local_context,
            &kernel_context,
        );

        // c0 = c0 matches x0 = x0
        let lit = Literal::parse("c0 = c0");
        assert!(
            set.find_generalization(&lit, &local_context, &kernel_context)
                .unwrap()
                .0
        );
    }

    #[test]
    fn test_literal_set_literal_reversing() {
        let local_context = test_local_context(10);
        // Use Bool types for all symbols
        let kernel_context =
            KernelContext::test_with_scoped_constant_types(&[BOOL, BOOL, BOOL, BOOL, BOOL]);

        let mut set = LiteralSet::new();
        // Test that x0 = x1 can match c0 = c1 (variables can be instantiated)
        set.insert(
            &Literal::parse("x0 = x1"),
            7,
            &local_context,
            &kernel_context,
        );
        let lit = Literal::parse("c0 = c1");
        assert!(
            set.find_generalization(&lit, &local_context, &kernel_context)
                .unwrap()
                .0
        );
    }
}
