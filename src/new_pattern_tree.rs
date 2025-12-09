// NewPatternTree: A pattern tree that uses curried representation and ClosedType for type matching.
//
// Unlike the original PatternTree which uses TypeId for type discrimination, this implementation
// represents types as terms and traverses them during matching. This allows pattern matching
// with type variables like List[T] without requiring every type to have a TypeId.
//
// Key design decisions:
// 1. Everything is curried - applications are binary, no num_args
// 2. Types are traversed like terms - same edges work for both
// 3. Variables are numbered by first occurrence (not de Bruijn indices)
// 4. Domain type appears before function/arg in application encoding

use qp_trie::{Entry, SubTrie, Trie};

use crate::kernel::aliases::{Clause, Literal, Term};
use crate::kernel::atom::{Atom as KernelAtom, AtomId};
use crate::kernel::closed_type::ClosedType;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::{TermComponent, TermRef};
use crate::kernel::types::{GroundTypeId, TypeId, TypeclassId};

/// Atoms are the leaf nodes in the pattern tree.
/// Both term variables and type variables are represented as Variable(idx).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Atom {
    /// Pattern variable, numbered by first occurrence in the path.
    /// Used for both term variables and type variables.
    Variable(AtomId),

    /// Named constants and functions.
    Symbol(Symbol),

    /// Ground types like Bool, Int, Nat.
    Type(GroundTypeId),

    /// The sort of types (kind *).
    /// Used as the domain for type constructors like List.
    Type0,

    /// Typeclass constraints like Monoid, CommRing.
    /// Used for constrained type variables.
    Typeclass(TypeclassId),

    /// Boolean constant true.
    True,
}

/// Edges form the structure of paths through the pattern tree.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Edge {
    // Structural edges (work for both terms and types)
    /// Application: followed by domain type, function, argument.
    /// For f(x) where f : T -> U, the path is: <U> Application <T> <f> <x>
    Application,

    /// Function type arrow: followed by domain, codomain.
    /// For Int -> Bool, the path is: Arrow <Int> <Bool>
    Arrow,

    /// A leaf atom.
    Atom(Atom),

    // Form edges (category markers for top-level discrimination)
    /// Indicates we're encoding a term.
    TermForm,

    /// Indicates we're encoding a pair of terms.
    TermPairForm,

    /// Indicates a literal with the given sign (true = positive).
    LiteralForm(bool),
}

// Byte constants for serialization
const APPLICATION: u8 = 0;
const ARROW: u8 = 1;
const TERM_FORM: u8 = 2;
const TERM_PAIR_FORM: u8 = 3;
const LITERAL_POSITIVE: u8 = 4;
const LITERAL_NEGATIVE: u8 = 5;
const ATOM_VARIABLE: u8 = 6;
const ATOM_TRUE: u8 = 7;
const ATOM_TYPE0: u8 = 8;
const ATOM_TYPE: u8 = 9;
const ATOM_TYPECLASS: u8 = 10;
const ATOM_SYMBOL_GLOBAL: u8 = 11;
const ATOM_SYMBOL_SCOPED: u8 = 12;
const ATOM_SYMBOL_MONOMORPH: u8 = 13;
const ATOM_SYMBOL_SYNTHETIC: u8 = 14;

impl Edge {
    /// Returns the discriminant byte for this edge.
    fn discriminant(&self) -> u8 {
        match self {
            Edge::Application => APPLICATION,
            Edge::Arrow => ARROW,
            Edge::TermForm => TERM_FORM,
            Edge::TermPairForm => TERM_PAIR_FORM,
            Edge::LiteralForm(true) => LITERAL_POSITIVE,
            Edge::LiteralForm(false) => LITERAL_NEGATIVE,
            Edge::Atom(atom) => match atom {
                Atom::Variable(_) => ATOM_VARIABLE,
                Atom::True => ATOM_TRUE,
                Atom::Type0 => ATOM_TYPE0,
                Atom::Type(_) => ATOM_TYPE,
                Atom::Typeclass(_) => ATOM_TYPECLASS,
                Atom::Symbol(Symbol::GlobalConstant(_)) => ATOM_SYMBOL_GLOBAL,
                Atom::Symbol(Symbol::ScopedConstant(_)) => ATOM_SYMBOL_SCOPED,
                Atom::Symbol(Symbol::Monomorph(_)) => ATOM_SYMBOL_MONOMORPH,
                Atom::Symbol(Symbol::Synthetic(_)) => ATOM_SYMBOL_SYNTHETIC,
            },
        }
    }

    /// Appends the byte representation of this edge to the vector.
    /// Each edge is 3 bytes: discriminant + 2 bytes for ID (if applicable).
    pub fn append_to(&self, v: &mut Vec<u8>) {
        v.push(self.discriminant());
        let id: u16 = match self {
            Edge::Application | Edge::Arrow | Edge::TermForm | Edge::TermPairForm => 0,
            Edge::LiteralForm(_) => 0,
            Edge::Atom(atom) => match atom {
                Atom::Variable(i) => *i,
                Atom::True => 0,
                Atom::Type0 => 0,
                Atom::Type(t) => t.as_u16(),
                Atom::Typeclass(tc) => tc.as_u16(),
                Atom::Symbol(Symbol::GlobalConstant(c)) => *c,
                Atom::Symbol(Symbol::ScopedConstant(c)) => *c,
                Atom::Symbol(Symbol::Monomorph(m)) => *m,
                Atom::Symbol(Symbol::Synthetic(s)) => *s,
            },
        };
        v.extend_from_slice(&id.to_ne_bytes());
    }

    /// Parses an edge from 3 bytes.
    pub fn from_bytes(byte1: u8, byte2: u8, byte3: u8) -> Edge {
        let id = u16::from_ne_bytes([byte2, byte3]);
        match byte1 {
            APPLICATION => Edge::Application,
            ARROW => Edge::Arrow,
            TERM_FORM => Edge::TermForm,
            TERM_PAIR_FORM => Edge::TermPairForm,
            LITERAL_POSITIVE => Edge::LiteralForm(true),
            LITERAL_NEGATIVE => Edge::LiteralForm(false),
            ATOM_VARIABLE => Edge::Atom(Atom::Variable(id)),
            ATOM_TRUE => Edge::Atom(Atom::True),
            ATOM_TYPE0 => Edge::Atom(Atom::Type0),
            ATOM_TYPE => Edge::Atom(Atom::Type(GroundTypeId::new(id))),
            ATOM_TYPECLASS => Edge::Atom(Atom::Typeclass(TypeclassId::new(id))),
            ATOM_SYMBOL_GLOBAL => Edge::Atom(Atom::Symbol(Symbol::GlobalConstant(id))),
            ATOM_SYMBOL_SCOPED => Edge::Atom(Atom::Symbol(Symbol::ScopedConstant(id))),
            ATOM_SYMBOL_MONOMORPH => Edge::Atom(Atom::Symbol(Symbol::Monomorph(id))),
            ATOM_SYMBOL_SYNTHETIC => Edge::Atom(Atom::Symbol(Symbol::Synthetic(id))),
            _ => panic!("invalid edge discriminant: {}", byte1),
        }
    }

    /// Debug helper to convert a byte sequence to a string of edges.
    pub fn debug_bytes(bytes: &[u8]) -> String {
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

/// Encodes a ClosedType into the key buffer.
/// Types are encoded as terms:
/// - Ground types: Atom(Type(id))
/// - Arrow types: Arrow + domain encoding + codomain encoding
/// - Type applications: Application + sort + head encoding + arg encoding
fn key_from_closed_type(closed_type: &ClosedType, key: &mut Vec<u8>) {
    key_from_closed_type_at(closed_type.components(), 0, key)
}

/// Encodes a ClosedType starting at the given position.
fn key_from_closed_type_at(components: &[TermComponent], pos: usize, key: &mut Vec<u8>) {
    match &components[pos] {
        TermComponent::Pi { span: _ } => {
            // Arrow type: domain -> codomain
            Edge::Arrow.append_to(key);
            // Find where domain ends
            let domain_end = find_subterm_end(components, pos + 1);
            key_from_closed_type_at(components, pos + 1, key);
            key_from_closed_type_at(components, domain_end, key);
        }
        TermComponent::Application { span } => {
            // Type application like List[Int]
            // Format: Application + <sort of result> + <head> + <args>
            // For now, we assume type applications produce Type0 (kind *)
            Edge::Application.append_to(key);
            Edge::Atom(Atom::Type0).append_to(key);

            // Encode head
            let head_end = find_subterm_end(components, pos + 1);
            key_from_closed_type_at(components, pos + 1, key);

            // Encode arguments
            let total_span = *span as usize;
            let mut arg_pos = head_end;
            while arg_pos < pos + total_span {
                key_from_closed_type_at(components, arg_pos, key);
                arg_pos = find_subterm_end(components, arg_pos);
            }
        }
        TermComponent::Atom(atom) => {
            let edge_atom = match atom {
                KernelAtom::Type(t) => Atom::Type(*t),
                KernelAtom::Variable(v) => Atom::Variable(*v),
                KernelAtom::True => Atom::True,
                KernelAtom::Symbol(s) => Atom::Symbol(*s),
            };
            Edge::Atom(edge_atom).append_to(key);
        }
    }
}

/// Find the end position of a subterm in components starting at `start`.
fn find_subterm_end(components: &[TermComponent], start: usize) -> usize {
    match components[start] {
        TermComponent::Pi { span } | TermComponent::Application { span } => start + span as usize,
        TermComponent::Atom(_) => start + 1,
    }
}

/// Encodes a term into the key buffer (without the form prefix).
/// This is a curried representation where applications are binary.
///
/// For atomic term `c : T`: type encoding + Atom(c)
/// For application `f(x)` where `f : A -> B`, `x : A`, result `B`:
///   type B encoding + Application + type A encoding + f encoding + x encoding
fn key_from_term_helper(
    term: TermRef,
    key: &mut Vec<u8>,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) {
    // Get the closed type of the term
    let term_closed_type = term.get_closed_type_with_context(local_context, kernel_context);

    if !term.has_args() {
        // Atomic term: type encoding + atom
        key_from_closed_type(&term_closed_type, key);
        let head = term.get_head_atom();
        let atom = match head {
            KernelAtom::Variable(v) => Atom::Variable(*v),
            KernelAtom::True => Atom::True,
            KernelAtom::Symbol(s) => Atom::Symbol(*s),
            KernelAtom::Type(t) => Atom::Type(*t),
        };
        Edge::Atom(atom).append_to(key);
    } else {
        // Application term: encode as curried binary applications
        // f(a, b, c) = ((f a) b) c
        // We need to encode from the outermost result type inward

        // First, emit the result type of the whole term
        key_from_closed_type(&term_closed_type, key);

        // Now encode the curried applications
        // For f(a1, a2, ..., an), we need:
        // Application + domain_n + [encoding of f(a1,...,a_{n-1})] + [encoding of an]
        key_from_curried_application(term, key, local_context, kernel_context);
    }
}

/// Helper to encode a term with arguments as curried applications.
/// Assumes the result type has already been emitted.
fn key_from_curried_application(
    term: TermRef,
    key: &mut Vec<u8>,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) {
    let args: Vec<TermRef> = term.iter_args().collect();
    if args.is_empty() {
        // Base case: just the head atom
        let head = term.get_head_atom();
        let atom = match head {
            KernelAtom::Variable(v) => Atom::Variable(*v),
            KernelAtom::True => Atom::True,
            KernelAtom::Symbol(s) => Atom::Symbol(*s),
            KernelAtom::Type(t) => Atom::Type(*t),
        };
        Edge::Atom(atom).append_to(key);
    } else {
        // Recursive case: Application + domain + func + arg
        let last_arg = args[args.len() - 1];
        let last_arg_type = last_arg.get_closed_type_with_context(local_context, kernel_context);

        Edge::Application.append_to(key);
        key_from_closed_type(&last_arg_type, key);

        // Encode the function part (term without last argument)
        if args.len() == 1 {
            // Just the head
            let head = term.get_head_atom();
            let atom = match head {
                KernelAtom::Variable(v) => Atom::Variable(*v),
                KernelAtom::True => Atom::True,
                KernelAtom::Symbol(s) => Atom::Symbol(*s),
                KernelAtom::Type(t) => Atom::Type(*t),
            };
            Edge::Atom(atom).append_to(key);
        } else {
            // Recurse for f(a1, ..., a_{n-1})
            // We need to create a virtual term with one fewer argument
            // For now, we'll encode iteratively
            key_from_partial_application(term, args.len() - 1, key, local_context, kernel_context);
        }

        // Encode the argument
        key_from_term_helper(last_arg, key, local_context, kernel_context);
    }
}

/// Encode a partial application of term, using only the first `num_args` arguments.
fn key_from_partial_application(
    term: TermRef,
    num_args: usize,
    key: &mut Vec<u8>,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) {
    if num_args == 0 {
        // Just the head
        let head = term.get_head_atom();
        let atom = match head {
            KernelAtom::Variable(v) => Atom::Variable(*v),
            KernelAtom::True => Atom::True,
            KernelAtom::Symbol(s) => Atom::Symbol(*s),
            KernelAtom::Type(t) => Atom::Type(*t),
        };
        Edge::Atom(atom).append_to(key);
    } else {
        let args: Vec<TermRef> = term.iter_args().take(num_args).collect();
        let last_arg = args[num_args - 1];
        let last_arg_type = last_arg.get_closed_type_with_context(local_context, kernel_context);

        Edge::Application.append_to(key);
        key_from_closed_type(&last_arg_type, key);

        // Recurse for the function part
        key_from_partial_application(term, num_args - 1, key, local_context, kernel_context);

        // Encode the argument
        key_from_term_helper(last_arg, key, local_context, kernel_context);
    }
}

/// Creates a key prefix for a term of the given type.
/// Takes both TypeId and ClosedType for API compatibility between old and new pattern trees.
/// The old implementation uses type_id, the new implementation uses closed_type.
///
/// Note: This only adds the TermForm marker, not the type encoding.
/// The type encoding is added by find_term_matches_while when matching.
pub fn term_key_prefix(_type_id: TypeId, _closed_type: &ClosedType) -> Vec<u8> {
    let mut key = Vec::new();
    Edge::TermForm.append_to(&mut key);
    key
}

/// Generates a complete key for a term.
pub fn key_from_term(
    term: &Term,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Vec<u8> {
    let mut key = Vec::new();
    Edge::TermForm.append_to(&mut key);
    key_from_term_helper(term.as_ref(), &mut key, local_context, kernel_context);
    key
}

/// Creates a key prefix for a term pair (like a literal).
pub fn term_pair_key_prefix(closed_type: &ClosedType) -> Vec<u8> {
    let mut key = Vec::new();
    Edge::TermPairForm.append_to(&mut key);
    key_from_closed_type(closed_type, &mut key);
    key
}

/// Generates a complete key for a term pair.
pub fn key_from_pair(
    term1: &Term,
    term2: &Term,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Vec<u8> {
    let type1 = term1.get_closed_type_with_context(local_context, kernel_context);
    let mut key = Vec::new();
    Edge::TermPairForm.append_to(&mut key);
    key_from_closed_type(&type1, &mut key);
    key_from_term_helper(term1.as_ref(), &mut key, local_context, kernel_context);
    key_from_term_helper(term2.as_ref(), &mut key, local_context, kernel_context);
    key
}

/// Generates a key prefix for a literal (based on sign and type).
pub fn literal_key_prefix(positive: bool, closed_type: &ClosedType) -> Vec<u8> {
    let mut key = Vec::new();
    Edge::LiteralForm(positive).append_to(&mut key);
    key_from_closed_type(closed_type, &mut key);
    key
}

/// Generates a complete key for a literal.
pub fn key_from_literal(
    literal: &Literal,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Vec<u8> {
    let type_left = literal
        .left
        .get_closed_type_with_context(local_context, kernel_context);
    let mut key = Vec::new();
    Edge::LiteralForm(literal.positive).append_to(&mut key);
    key_from_closed_type(&type_left, &mut key);
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
    key
}

/// Creates a key prefix for a clause based on its literals' signs and types.
fn clause_key_prefix(clause: &Clause, kernel_context: &KernelContext) -> Vec<u8> {
    let local_context = clause.get_local_context();
    let mut key = Vec::new();
    for literal in &clause.literals {
        let type_left = literal
            .left
            .get_closed_type_with_context(local_context, kernel_context);
        Edge::LiteralForm(literal.positive).append_to(&mut key);
        key_from_closed_type(&type_left, &mut key);
    }
    key
}

/// Generates a complete key for a clause.
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

/// NewPatternTree: A pattern tree using curried representation and ClosedType for type matching.
///
/// This is designed to eventually replace PatternTree, supporting type variables in patterns.
#[derive(Clone, Debug)]
pub struct NewPatternTree<T> {
    /// Maps byte keys to indices into the values vector.
    trie: Trie<Vec<u8>, usize>,

    /// Values stored in the tree.
    pub values: Vec<T>,
}

impl<T> NewPatternTree<T> {
    pub fn new() -> NewPatternTree<T> {
        NewPatternTree {
            trie: Trie::new(),
            values: vec![],
        }
    }

    /// Inserts a term with its associated value.
    pub fn insert_term(
        &mut self,
        term: &Term,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        let key = key_from_term(term, local_context, kernel_context);
        let value_id = self.values.len();
        self.values.push(value);
        self.trie.insert(key, value_id);
    }

    /// Inserts a term pair (like a literal without sign) with its associated value.
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

    /// Inserts a clause with its associated value.
    pub fn insert_clause(&mut self, clause: &Clause, value: T, kernel_context: &KernelContext) {
        let key = key_from_clause(clause, kernel_context);
        let value_id = self.values.len();
        self.values.push(value);
        self.trie.insert(key, value_id);
    }

    /// Finds matches for a term, calling the callback for each match.
    /// Returns false if callback returns false, otherwise true.
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
            100, // stack limit
            replacements,
            callback,
        )
    }

    /// Finds a pair (like a literal) in the tree.
    pub fn find_pair<'a>(
        &'a self,
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<&'a T> {
        let type_left = left.get_closed_type_with_context(local_context, kernel_context);
        let mut key = term_pair_key_prefix(&type_left);
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

    /// Finds a clause in the tree.
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

impl NewPatternTree<()> {
    /// Appends to the existing value if possible. Otherwise, inserts a vec![U].
    pub fn insert_or_append<U>(
        pt: &mut NewPatternTree<Vec<U>>,
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

/// The NewLiteralSet stores literals using the new curried pattern tree.
/// It provides the same interface as LiteralSet but uses NewPatternTree internally.
#[derive(Clone)]
pub struct NewLiteralSet {
    /// Stores (sign, id, flipped) for each literal.
    tree: NewPatternTree<(bool, usize, bool)>,
}

impl NewLiteralSet {
    pub fn new() -> NewLiteralSet {
        NewLiteralSet {
            tree: NewPatternTree::new(),
        }
    }

    /// Inserts a literal along with its id.
    /// This always inserts the left->right direction.
    /// When the literal is strictly kbo ordered, it can't be reversed and unify with
    /// another literal, so we don't need to insert the right->left direction.
    /// Otherwise, we do insert the right->left direction.
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

/// Helper function to match curried application structure.
/// This handles the case where we have a term f(a1, a2, ..., an) and need to match
/// the curried encoding against patterns.
///
/// At this point, we've already matched:
/// - The result type
/// - The Application edge
/// - The domain type of the last argument
///
/// Now we need to match the "function part" (f applied to all but the last arg)
/// followed by the last argument, followed by rest.
fn match_curried_application<'a, F>(
    subtrie: &SubTrie<Vec<u8>, usize>,
    key: &mut Vec<u8>,
    term: TermRef<'a>,
    num_args: usize,
    rest: &[TermRef<'a>],
    local_context: &LocalContext,
    kernel_context: &KernelContext,
    stack_limit: usize,
    replacements: &mut Vec<TermRef<'a>>,
    callback: &mut F,
) -> bool
where
    F: FnMut(usize, &Vec<TermRef<'a>>) -> bool,
{
    if subtrie.is_empty() || stack_limit == 0 {
        return true;
    }

    let args: Vec<TermRef<'a>> = term.iter_args().take(num_args).collect();
    let last_arg = args[num_args - 1];
    let head_atom = term.get_head_atom();

    if num_args == 1 {
        // Base case: just the head atom, then the argument
        // We need to handle two cases:
        // 1. The pattern has a variable in function position (e.g., x0(c5))
        //    - The head symbol can match against the pattern variable
        // 2. The pattern has a specific atom in function position (e.g., c1(x0))
        //    - We need exact match of the atom

        let initial_key_len = key.len();
        let mut next_terms: Vec<TermRef<'a>> = vec![last_arg];
        next_terms.extend_from_slice(rest);

        // Case A: Try matching the head against a new pattern variable
        // This enables matching c1(c5) against pattern x0(c5) where x0 : Bool -> Bool
        // In the pattern, x0 is just Variable(0) without type prefix in function position
        if !head_atom.is_variable() {
            Edge::Atom(Atom::Variable(replacements.len() as u16)).append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);
            if !new_subtrie.is_empty() {
                // The pattern has a variable at this position - push the head term
                // We need to represent "just the head" as a term for the replacement
                // Since the head is atomic, we can get a reference to it from the term
                let head_term = term.get_head_subterm();
                replacements.push(head_term);
                if !find_term_matches_while(
                    &new_subtrie,
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
                replacements.pop();
            }
            key.truncate(initial_key_len);
        }

        // Case B: Exact match - emit the specific atom
        let atom = match head_atom {
            KernelAtom::Variable(v) => Atom::Variable(*v),
            KernelAtom::True => Atom::True,
            KernelAtom::Symbol(s) => Atom::Symbol(*s),
            KernelAtom::Type(t) => Atom::Type(*t),
        };
        Edge::Atom(atom).append_to(key);
        let new_subtrie = subtrie.subtrie(key as &[u8]);

        return find_term_matches_while(
            &new_subtrie,
            key,
            &next_terms,
            local_context,
            kernel_context,
            stack_limit - 1,
            replacements,
            callback,
        );
    }

    // Recursive case: more than one argument
    // Need to match: Application + domain_{n-1} + [f(a1,...,a_{n-2})] + [a_{n-1}] + [a_n] + rest
    //
    // But wait - we've already stripped off the last arg.
    // So we need to match the "function" f(a1,...,a_{n-1}) structure,
    // then put the last_arg and rest back on the terms list.

    // Match Application edge for the inner application
    Edge::Application.append_to(key);
    let new_subtrie = subtrie.subtrie(key as &[u8]);

    // Match domain type of argument n-1
    let prev_arg = args[num_args - 2];
    let prev_arg_type = prev_arg.get_closed_type_with_context(local_context, kernel_context);
    key_from_closed_type(&prev_arg_type, key);
    let new_subtrie2 = new_subtrie.subtrie(key as &[u8]);

    // Recursively match the rest of the curried structure
    // After matching all the way down, we'll have last_arg + rest to match
    let mut next_rest: Vec<TermRef<'a>> = vec![last_arg];
    next_rest.extend_from_slice(rest);

    match_curried_application(
        &new_subtrie2,
        key,
        term,
        num_args - 1,
        &next_rest,
        local_context,
        kernel_context,
        stack_limit - 1,
        replacements,
        callback,
    )
}

/// Matching implementation for the new pattern tree.
/// Matches a sequence of terms against patterns in the trie.
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
            // Need to emit type encoding first, then the variable
            let term_type = first.get_closed_type_with_context(local_context, kernel_context);
            key_from_closed_type(&term_type, key);
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
    // We need to emit the type encoding first, then the variable
    let term_type = first.get_closed_type_with_context(local_context, kernel_context);
    key_from_closed_type(&term_type, key);
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

    // Case 3: exact match - match the structure of the term
    let head_atom = first.get_head_atom();
    if head_atom.is_variable() {
        // Variables in the query term must match via Cases 1 or 2, not exact match
        return true;
    }

    // Get the result type and match it
    let term_type = first.get_closed_type_with_context(local_context, kernel_context);
    key_from_closed_type(&term_type, key);

    if !first.has_args() {
        // Atomic term: match the atom
        let atom = match head_atom {
            KernelAtom::Variable(v) => Atom::Variable(*v),
            KernelAtom::True => Atom::True,
            KernelAtom::Symbol(s) => Atom::Symbol(*s),
            KernelAtom::Type(t) => Atom::Type(*t),
        };
        Edge::Atom(atom).append_to(key);
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
    } else {
        // Application term: match the curried structure
        // For f(a1, a2, ..., an), the encoding is:
        // <result type> + Application + <domain_n> + [...f(a1,...,a_{n-1})...] + [...an...]
        // We match: Application edge, domain type, then recurse with head-with-fewer-args and last-arg

        // Collect arguments
        let args: Vec<TermRef<'a>> = first.iter_args().collect();
        let last_arg = args[args.len() - 1];
        let last_arg_type = last_arg.get_closed_type_with_context(local_context, kernel_context);

        // Match Application edge
        Edge::Application.append_to(key);
        let new_subtrie = subtrie.subtrie(key as &[u8]);

        // Match domain type
        key_from_closed_type(&last_arg_type, key);
        let new_subtrie2 = new_subtrie.subtrie(key as &[u8]);

        if args.len() == 1 {
            // Just the head atom, then the argument
            // We need to handle two cases:
            // Case A: The pattern has a variable in function position (e.g., x0(c5))
            //         The head symbol can match against the pattern variable
            // Case B: The pattern has a specific atom in function position (e.g., c1(x0))
            //         We need exact match of the atom

            let key_len_after_domain = key.len();
            let mut next_terms: Vec<TermRef<'a>> = vec![last_arg];
            next_terms.extend_from_slice(rest);

            // Case A: Try matching the head against a new pattern variable
            // This enables matching c1(c5) against pattern x0(c5) where x0 : Bool -> Bool
            if !head_atom.is_variable() {
                Edge::Atom(Atom::Variable(replacements.len() as u16)).append_to(key);
                let var_subtrie = new_subtrie2.subtrie(key as &[u8]);
                if !var_subtrie.is_empty() {
                    // The pattern has a variable at this position
                    // Push the head term as a replacement
                    let head_term = first.get_head_subterm();
                    replacements.push(head_term);
                    if !find_term_matches_while(
                        &var_subtrie,
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
                    replacements.pop();
                }
                key.truncate(key_len_after_domain);
            }

            // Case B: Exact match of the head atom
            let atom = match head_atom {
                KernelAtom::Variable(v) => Atom::Variable(*v),
                KernelAtom::True => Atom::True,
                KernelAtom::Symbol(s) => Atom::Symbol(*s),
                KernelAtom::Type(t) => Atom::Type(*t),
            };
            Edge::Atom(atom).append_to(key);
            let new_subtrie3 = new_subtrie2.subtrie(key as &[u8]);

            if !find_term_matches_while(
                &new_subtrie3,
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
            // Multiple args: we need to handle two cases:
            // Case A: The pattern has a variable at the function position.
            //         The partial application (all args except the last) matches the variable.
            // Case B: The pattern has a specific structure at the function position.
            //         We recursively match the curried structure.

            let key_len_after_domain = key.len();
            let mut remaining_terms: Vec<TermRef<'a>> = vec![last_arg];
            remaining_terms.extend_from_slice(rest);

            // Case A: Try matching the partial application against a new pattern variable
            // This enables matching c0(c7, c5) against pattern x0(c5) where x0 : Bool -> Bool
            // The partial application c0(c7) should match variable x0
            if !head_atom.is_variable() {
                Edge::Atom(Atom::Variable(replacements.len() as u16)).append_to(key);
                let var_subtrie = new_subtrie2.subtrie(key as &[u8]);
                if !var_subtrie.is_empty() {
                    // The pattern has a variable at this position
                    // Push the partial application as a replacement
                    let partial_app = first.get_partial_application(args.len() - 1);
                    replacements.push(partial_app);
                    if !find_term_matches_while(
                        &var_subtrie,
                        key,
                        &remaining_terms,
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
                key.truncate(key_len_after_domain);
            }

            // Case B: Match the curried structure exactly
            if !match_curried_application(
                &new_subtrie2,
                key,
                first,
                args.len(),
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
    }

    key.truncate(initial_key_len);
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::type_store::TypeStore;
    use crate::kernel::types::BOOL;

    #[test]
    fn test_edge_roundtrip() {
        let edges = vec![
            Edge::Application,
            Edge::Arrow,
            Edge::TermForm,
            Edge::TermPairForm,
            Edge::LiteralForm(true),
            Edge::LiteralForm(false),
            Edge::Atom(Atom::Variable(0)),
            Edge::Atom(Atom::Variable(42)),
            Edge::Atom(Atom::True),
            Edge::Atom(Atom::Type0),
            Edge::Atom(Atom::Type(GroundTypeId::new(1))),
            Edge::Atom(Atom::Type(GroundTypeId::new(100))),
            Edge::Atom(Atom::Typeclass(TypeclassId::new(5))),
            Edge::Atom(Atom::Symbol(Symbol::GlobalConstant(10))),
            Edge::Atom(Atom::Symbol(Symbol::ScopedConstant(20))),
            Edge::Atom(Atom::Symbol(Symbol::Monomorph(30))),
            Edge::Atom(Atom::Symbol(Symbol::Synthetic(40))),
        ];

        for edge in edges {
            let mut bytes = Vec::new();
            edge.append_to(&mut bytes);
            assert_eq!(bytes.len(), 3);
            let parsed = Edge::from_bytes(bytes[0], bytes[1], bytes[2]);
            assert_eq!(edge, parsed, "roundtrip failed for {:?}", edge);
        }
    }

    #[test]
    fn test_debug_bytes() {
        let mut bytes = Vec::new();
        Edge::TermForm.append_to(&mut bytes);
        Edge::Atom(Atom::Type(GroundTypeId::new(1))).append_to(&mut bytes);
        Edge::Atom(Atom::Symbol(Symbol::ScopedConstant(5))).append_to(&mut bytes);

        let debug = Edge::debug_bytes(&bytes);
        assert!(debug.contains("TermForm"));
        assert!(debug.contains("Type"));
        assert!(debug.contains("ScopedConstant"));
    }

    #[test]
    fn test_key_from_closed_type_ground() {
        let store = TypeStore::new();
        let bool_ground = store.get_ground_type_id(BOOL).unwrap();

        // Test encoding of a ground type like Bool
        let bool_type = ClosedType::ground(bool_ground);
        let mut key = Vec::new();
        key_from_closed_type(&bool_type, &mut key);

        // Should be just Atom(Type(bool_ground))
        assert_eq!(key.len(), 3);
        let edge = Edge::from_bytes(key[0], key[1], key[2]);
        assert_eq!(edge, Edge::Atom(Atom::Type(bool_ground)));
    }

    #[test]
    fn test_key_from_closed_type_arrow() {
        let store = TypeStore::new();
        let bool_ground = store.get_ground_type_id(BOOL).unwrap();

        // Test encoding of Bool -> Bool
        let bool_type = ClosedType::ground(bool_ground);
        let arrow_type = ClosedType::pi(bool_type.clone(), bool_type.clone());
        let mut key = Vec::new();
        key_from_closed_type(&arrow_type, &mut key);

        // Should be: Arrow + Atom(Type(bool_ground)) + Atom(Type(bool_ground))
        assert_eq!(key.len(), 9);

        let edge1 = Edge::from_bytes(key[0], key[1], key[2]);
        assert_eq!(edge1, Edge::Arrow);

        let edge2 = Edge::from_bytes(key[3], key[4], key[5]);
        assert_eq!(edge2, Edge::Atom(Atom::Type(bool_ground)));

        let edge3 = Edge::from_bytes(key[6], key[7], key[8]);
        assert_eq!(edge3, Edge::Atom(Atom::Type(bool_ground)));
    }

    #[test]
    fn test_key_from_term_atomic() {
        // Test encoding of an atomic term c0 : Bool
        let local_context = LocalContext::new(vec![BOOL; 2]);
        let kernel_context =
            KernelContext::test_with_scoped_constant_types(&[BOOL, BOOL, BOOL, BOOL, BOOL]);

        let term = Term::parse("c0");
        let key = key_from_term(&term, &local_context, &kernel_context);

        // Should be: TermForm + Type(BOOL) + Type(BOOL) + Atom(ScopedConstant(0))
        // Wait, I need to check the actual encoding...
        // The key starts with TermForm, then the term's encoding
        // For an atomic term: type + atom
        // So: TermForm + Type(BOOL) + Atom(c0)
        let debug = Edge::debug_bytes(&key);
        assert!(debug.contains("TermForm"), "key: {}", debug);
        assert!(debug.contains("Type"), "key: {}", debug);
        assert!(debug.contains("ScopedConstant"), "key: {}", debug);
    }

    #[test]
    fn test_key_from_literal() {
        // Test encoding of x0 = c0
        let local_context = LocalContext::new(vec![BOOL; 2]);
        let kernel_context =
            KernelContext::test_with_scoped_constant_types(&[BOOL, BOOL, BOOL, BOOL, BOOL]);

        let literal = Literal::parse("x0 = c0");
        let key = key_from_literal(&literal, &local_context, &kernel_context);

        // Should start with LiteralForm(true) since it's positive
        let edge1 = Edge::from_bytes(key[0], key[1], key[2]);
        assert_eq!(edge1, Edge::LiteralForm(true));

        // Should contain the type and both terms
        let debug = Edge::debug_bytes(&key);
        assert!(debug.contains("LiteralForm(true)"), "key: {}", debug);
    }

    #[test]
    fn test_new_pattern_tree_insert_term() {
        // Test inserting and finding atomic terms
        let local_context = LocalContext::new(vec![BOOL; 2]);
        let kernel_context =
            KernelContext::test_with_scoped_constant_types(&[BOOL, BOOL, BOOL, BOOL, BOOL]);

        let mut tree: NewPatternTree<usize> = NewPatternTree::new();

        // Insert c0
        let term = Term::parse("c0");
        tree.insert_term(&term, 42, &local_context, &kernel_context);

        assert_eq!(tree.values.len(), 1);
        assert_eq!(tree.values[0], 42);
    }

    #[test]
    fn test_new_pattern_tree_insert_pair() {
        // Test inserting term pairs
        let local_context = LocalContext::new(vec![BOOL; 2]);
        let kernel_context =
            KernelContext::test_with_scoped_constant_types(&[BOOL, BOOL, BOOL, BOOL, BOOL]);

        let mut tree: NewPatternTree<usize> = NewPatternTree::new();

        // Insert (c0, c1)
        let term1 = Term::parse("c0");
        let term2 = Term::parse("c1");
        tree.insert_pair(&term1, &term2, 99, &local_context, &kernel_context);

        assert_eq!(tree.values.len(), 1);
        assert_eq!(tree.values[0], 99);

        // Should find the pair
        let found = tree.find_pair(&term1, &term2, &local_context, &kernel_context);
        assert_eq!(found, Some(&99));

        // Should not find a different pair
        let term3 = Term::parse("c2");
        let not_found = tree.find_pair(&term1, &term3, &local_context, &kernel_context);
        assert_eq!(not_found, None);
    }

    #[test]
    fn test_new_pattern_tree_variable_matching() {
        // Test that patterns with variables match concrete terms
        let local_context = LocalContext::new(vec![BOOL; 2]);
        let kernel_context =
            KernelContext::test_with_scoped_constant_types(&[BOOL, BOOL, BOOL, BOOL, BOOL]);

        let mut tree: NewPatternTree<usize> = NewPatternTree::new();

        // Insert pattern "x0 = c0" - a variable equals a constant
        let pattern_left = Term::parse("x0");
        let pattern_right = Term::parse("c0");
        tree.insert_pair(
            &pattern_left,
            &pattern_right,
            7,
            &local_context,
            &kernel_context,
        );

        // Query "c1 = c0" should match (c1 can be matched by variable x0)
        let query_left = Term::parse("c1");
        let query_right = Term::parse("c0");
        let found = tree.find_pair(&query_left, &query_right, &local_context, &kernel_context);
        assert_eq!(found, Some(&7));
    }

    #[test]
    fn test_new_pattern_tree_application_with_variable() {
        // Test that patterns with function applications and variables match correctly
        // c1 : Bool -> Bool, so c1(x0) : Bool when x0 : Bool
        let local_context = LocalContext::new(vec![BOOL; 3]);
        let kernel_context = KernelContext::test_with_function_types();

        let mut tree: NewPatternTree<usize> = NewPatternTree::new();

        // Insert pattern "c1(x0) = c5" - a function applied to a variable equals a constant
        // c1 : Bool -> Bool, c5 : Bool
        let pattern_left = Term::parse("c1(x0)");
        let pattern_right = Term::parse("c5");
        tree.insert_pair(
            &pattern_left,
            &pattern_right,
            42,
            &local_context,
            &kernel_context,
        );

        // Query "c1(c6) = c5" should match (c6 : Bool can be matched by variable x0)
        // c6 : Bool
        let query_left = Term::parse("c1(c6)");
        let query_right = Term::parse("c5");
        let found = tree.find_pair(&query_left, &query_right, &local_context, &kernel_context);
        assert_eq!(found, Some(&42));
    }

    #[test]
    fn test_new_pattern_tree_clause_with_function_application() {
        // Test that clauses with function applications can be inserted and found
        // when using test_with_function_types which properly stores Pi types.
        let local_context = LocalContext::new(vec![BOOL; 3]);
        let kernel_context = KernelContext::test_with_function_types();

        let mut tree: NewPatternTree<usize> = NewPatternTree::new();

        // Create a clause with a function application: c1(x0) = c5
        // c1 : Bool -> Bool, c5 : Bool
        let clause = Clause::parse("c1(x0) = c5", &local_context);
        tree.insert_clause(&clause, 42, &kernel_context);

        // Should be able to find the exact same clause
        let found = tree.find_clause(&clause, &kernel_context);
        assert_eq!(found, Some(&42));
    }

    #[test]
    fn test_new_pattern_tree_clause_specialization() {
        // Test that find_clause can match a specialized clause against a pattern.
        // Note: find_clause does exact structural matching with variable substitution.
        // The clauses must have the same structure (same left/right order).
        //
        // Clause parsing normalizes literals by KBO, which can flip left/right.
        // So we use clauses where the structure is preserved.
        let local_context = LocalContext::new(vec![BOOL; 3]);
        let kernel_context = KernelContext::test_with_function_types();

        let mut tree: NewPatternTree<usize> = NewPatternTree::new();

        // Insert pattern: x0 = c5 (variable on left, constant on right)
        // After KBO normalization, x0 < c5 so this might get flipped.
        // Let's use a simpler case where structure is predictable.
        let clause = Clause::parse("x0 = x0", &local_context);
        tree.insert_clause(&clause, 42, &kernel_context);

        // Query: c5 = c5 should match (c5 substituted for x0)
        let special = Clause::parse("c5 = c5", &local_context);
        let found_special = tree.find_clause(&special, &kernel_context);
        assert_eq!(found_special, Some(&42));
    }

    #[test]
    fn test_new_pattern_tree_clause_multi_literal() {
        // Test clause with multiple literals containing function applications
        let local_context = LocalContext::new(vec![BOOL; 3]);
        let kernel_context = KernelContext::test_with_function_types();

        let mut tree: NewPatternTree<usize> = NewPatternTree::new();

        // Create a clause with two literals: c1(x0) = c5 or c0(x0, x1) = c6
        // c0 : (Bool, Bool) -> Bool, c1 : Bool -> Bool, c5, c6 : Bool
        let clause = Clause::parse("c1(x0) = c5 or c0(x0, x1) = c6", &local_context);
        tree.insert_clause(&clause, 99, &kernel_context);

        // Should be able to find the clause
        let found = tree.find_clause(&clause, &kernel_context);
        assert_eq!(found, Some(&99));
    }

    #[test]
    fn test_insert_or_append_and_find() {
        // Test the insert_or_append + find_term_matches_while pattern used by RewriteTree
        // Use test_with_all_bool_types to match what rewrite_tree tests use
        let local_context = LocalContext::new(vec![BOOL; 10]);
        let kernel_context = KernelContext::test_with_all_bool_types();

        let mut tree: NewPatternTree<Vec<usize>> = NewPatternTree::new();

        // Insert c1 using insert_or_append (like RewriteTree does)
        let term = Term::parse("c1");
        NewPatternTree::insert_or_append(&mut tree, &term, 42, &local_context, &kernel_context);

        // Now try to find it using the pattern that RewriteTree uses
        let type_id = term.get_term_type_with_context(&local_context, &kernel_context);
        let closed_type = term.get_closed_type_with_context(&local_context, &kernel_context);
        let mut key = term_key_prefix(type_id, &closed_type);

        let terms = [term.as_ref()];
        let mut replacements: Vec<TermRef> = vec![];
        let mut found_id = None;

        tree.find_term_matches_while(
            &mut key,
            &terms,
            &local_context,
            &kernel_context,
            &mut replacements,
            &mut |value_id, _| {
                found_id = Some(value_id);
                false
            },
        );

        assert!(found_id.is_some(), "Should find the inserted term");
        assert_eq!(tree.values[found_id.unwrap()], vec![42]);
    }

    #[test]
    fn test_curried_variable_matches_partial_application() {
        // Test that the new pattern tree can match a partial application against a function variable.
        // This is a key capability of curried representation that the old pattern tree doesn't have.
        //
        // Setup from test_with_function_types:
        // c0 : (Bool, Bool) -> Bool (2-arg function)
        // c1 : Bool -> Bool (1-arg function)
        // c5-c9 : Bool
        //
        // Pattern: x0(c6) where x0 : Bool -> Bool
        // Query: c0(c5, c6) = ((Bool, Bool) -> Bool)(Bool, Bool) = Bool
        //
        // In curried form:
        // - c0(c5, c6) becomes Application(Application(c0, c5), c6)
        // - x0(c6) becomes Application(x0, c6)
        //
        // The match should succeed with x0 = c0(c5), which has type Bool -> Bool.
        let kernel_context = KernelContext::test_with_function_types();

        // Create local context where x0 has type Bool -> Bool
        // c1 has type Bool -> Bool (scoped constant index 1)
        use crate::kernel::symbol::Symbol;
        let type_bool_to_bool = kernel_context
            .symbol_table
            .get_type(Symbol::ScopedConstant(1));
        let local_context =
            LocalContext::new_with_type_store(vec![type_bool_to_bool], &kernel_context.type_store);

        let mut tree: NewPatternTree<usize> = NewPatternTree::new();

        // Insert pattern: x0(c6) = c5
        let pattern_left = Term::parse("x0(c6)");
        let pattern_right = Term::parse("c5");
        tree.insert_pair(
            &pattern_left,
            &pattern_right,
            42,
            &local_context,
            &kernel_context,
        );

        // First verify that the partial application c0(c5) has type Bool -> Bool
        let partial_app = Term::parse("c0(c5)");
        let partial_type =
            partial_app.get_closed_type_with_context(&local_context, &kernel_context);
        let x0_type = local_context.get_var_closed_type(0);
        assert_eq!(
            partial_type,
            *x0_type.unwrap(),
            "c0(c5) should have the same type as x0 (Bool -> Bool)"
        );

        // Query: c0(c5, c6) = c5
        // c0(c5) is a partial application of type Bool -> Bool, which should match x0
        let query_left = Term::parse("c0(c5, c6)");
        let query_right = Term::parse("c5");
        let found = tree.find_pair(&query_left, &query_right, &local_context, &kernel_context);

        // The new pattern tree should find this match because:
        // - c0(c5, c6) curries to Application(Application(c0, c5), c6)
        // - Pattern x0(c6) curries to Application(x0, c6)
        // - x0 (a variable of type Bool -> Bool) can match Application(c0, c5)
        assert_eq!(
            found,
            Some(&42),
            "Curried matching should allow variable to match partial application"
        );
    }

    #[test]
    fn test_curried_variable_matches_different_arity() {
        // Another test demonstrating curried matching with different arities.
        //
        // Pattern: x0(c5) = c6 where x0 : Bool -> Bool, c5 : Bool
        // Query: c1(c5) = c6 where c1 : Bool -> Bool
        //
        // This should match with x0 = c1 (simple variable binding).
        let kernel_context = KernelContext::test_with_function_types();

        use crate::kernel::symbol::Symbol;
        let type_bool_to_bool = kernel_context
            .symbol_table
            .get_type(Symbol::ScopedConstant(1));
        let local_context =
            LocalContext::new_with_type_store(vec![type_bool_to_bool], &kernel_context.type_store);

        let mut tree: NewPatternTree<usize> = NewPatternTree::new();

        // Insert pattern: x0(c5) = c6
        let pattern_left = Term::parse("x0(c5)");
        let pattern_right = Term::parse("c6");
        tree.insert_pair(
            &pattern_left,
            &pattern_right,
            100,
            &local_context,
            &kernel_context,
        );

        // First verify c1 has type Bool -> Bool
        let c1_term = Term::parse("c1");
        let c1_type = c1_term.get_closed_type_with_context(&local_context, &kernel_context);
        let x0_type = local_context.get_var_closed_type(0);
        assert_eq!(
            c1_type,
            *x0_type.unwrap(),
            "c1 should have the same type as x0 (Bool -> Bool)"
        );

        // Debug: print what was inserted vs what we're querying
        let pattern_key = key_from_pair(
            &pattern_left,
            &pattern_right,
            &local_context,
            &kernel_context,
        );
        eprintln!("Pattern key: {}", Edge::debug_bytes(&pattern_key));

        // Query 1: c1(c5) = c6 - same arity, should match with x0 = c1
        let query1_left = Term::parse("c1(c5)");
        let query1_right = Term::parse("c6");
        let query1_key =
            key_from_pair(&query1_left, &query1_right, &local_context, &kernel_context);
        eprintln!("Query1 key: {}", Edge::debug_bytes(&query1_key));

        let found1 = tree.find_pair(&query1_left, &query1_right, &local_context, &kernel_context);
        assert_eq!(found1, Some(&100), "Same-arity application should match");

        // Query 2: c0(c7, c5) = c6 - different arity, but c0(c7) has type Bool -> Bool
        // So c0(c7, c5) = Application(Application(c0, c7), c5) should match x0(c5)
        // with x0 = c0(c7)
        let query2_left = Term::parse("c0(c7, c5)");
        let query2_right = Term::parse("c6");
        let found2 = tree.find_pair(&query2_left, &query2_right, &local_context, &kernel_context);
        assert_eq!(
            found2,
            Some(&100),
            "Different-arity application should match via currying"
        );
    }
}
