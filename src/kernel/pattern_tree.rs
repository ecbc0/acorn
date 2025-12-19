// PatternTree: A pattern tree that uses curried representation and Term types for type matching.
//
// Key design decisions:
// 1. Everything is curried - applications are binary, no num_args
// 2. Types are traversed like terms - same edges work for both
// 3. Variables are numbered by first occurrence (not de Bruijn indices)
// 4. Domain type appears before function/arg in application encoding

use qp_trie::{Entry, SubTrie, Trie};

use super::atom::{Atom as KernelAtom, AtomId};
use super::clause::Clause;
use super::kernel_context::KernelContext;
use super::literal::Literal;
use super::local_context::LocalContext;
use super::symbol::Symbol;
use super::term::Term;
use super::term::{Decomposition, TermRef};
use super::types::{GroundTypeId, TypeclassId};

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
    let mut output_types: Vec<Term> = replacement_context.get_var_types().to_vec();

    fn replace_recursive(
        term: TermRef,
        term_context: &LocalContext,
        replacements: &[TermRef],
        shift: Option<AtomId>,
        output_types: &mut Vec<Term>,
    ) -> Term {
        match term.decompose() {
            Decomposition::Atom(KernelAtom::FreeVariable(var_id)) => {
                let idx = *var_id as usize;
                if idx < replacements.len() {
                    // Replace with the replacement term
                    replacements[idx].to_owned()
                } else {
                    // Shift the variable
                    let new_var_id = match shift {
                        Some(s) => *var_id + s,
                        None => panic!("no replacement for variable x{}", var_id),
                    };
                    // Track the type for the shifted variable
                    let new_idx = new_var_id as usize;
                    let var_type = term_context
                        .get_var_type(idx)
                        .cloned()
                        .expect("variable type not found in term_context");
                    if new_idx >= output_types.len() {
                        output_types.resize(new_idx + 1, Term::empty_type());
                    }
                    output_types[new_idx] = var_type;
                    Term::atom(KernelAtom::FreeVariable(new_var_id))
                }
            }
            Decomposition::Atom(_) => term.to_owned(),
            Decomposition::Application(func, arg) => {
                let replaced_func =
                    replace_recursive(func, term_context, replacements, shift, output_types);
                let replaced_arg =
                    replace_recursive(arg, term_context, replacements, shift, output_types);
                replaced_func.apply(&[replaced_arg])
            }
            Decomposition::Pi(input, output) => {
                let replaced_input =
                    replace_recursive(input, term_context, replacements, shift, output_types);
                let replaced_output =
                    replace_recursive(output, term_context, replacements, shift, output_types);
                Term::pi(replaced_input, replaced_output)
            }
        }
    }

    let result_term = replace_recursive(
        term.as_ref(),
        term_context,
        replacements,
        shift,
        &mut output_types,
    );
    let result_context = LocalContext::from_types(output_types);
    (result_term, result_context)
}

/// Atoms are the leaf nodes in the pattern tree.
/// Both term variables and type variables are represented as Variable(idx).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Atom {
    /// Pattern variable, numbered by first occurrence in the path.
    /// Used for both term variables and type variables.
    Variable(AtomId),

    /// De Bruijn bound variable (for Pi types).
    BoundVariable(u16),

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

    /// Boolean constant false.
    False,
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

    /// Indicates a literal with the given sign (true = positive).
    LiteralForm(bool),
}

// Byte constants for serialization
const APPLICATION: u8 = 0;
const ARROW: u8 = 1;
const LITERAL_POSITIVE: u8 = 2;
const LITERAL_NEGATIVE: u8 = 3;
const ATOM_VARIABLE: u8 = 4;
const ATOM_TRUE: u8 = 5;
const ATOM_TYPE0: u8 = 6;
const ATOM_TYPE: u8 = 7;
const ATOM_TYPECLASS: u8 = 8;
const ATOM_SYMBOL_GLOBAL: u8 = 9;
const ATOM_SYMBOL_SCOPED: u8 = 10;
const ATOM_SYMBOL_SYNTHETIC: u8 = 12;
const ATOM_FALSE: u8 = 13;
const ATOM_SYMBOL_EMPTY: u8 = 14;
const ATOM_SYMBOL_BOOL: u8 = 15;
const ATOM_SYMBOL_TYPESORT: u8 = 16;
const ATOM_BOUND_VARIABLE: u8 = 17;

impl Edge {
    /// Returns the discriminant byte for this edge.
    fn discriminant(&self) -> u8 {
        match self {
            Edge::Application => APPLICATION,
            Edge::Arrow => ARROW,
            Edge::LiteralForm(true) => LITERAL_POSITIVE,
            Edge::LiteralForm(false) => LITERAL_NEGATIVE,
            Edge::Atom(atom) => match atom {
                Atom::Variable(_) => ATOM_VARIABLE,
                Atom::BoundVariable(_) => ATOM_BOUND_VARIABLE,
                Atom::True => ATOM_TRUE,
                Atom::False => ATOM_FALSE,
                Atom::Type0 => ATOM_TYPE0,
                Atom::Type(_) => ATOM_TYPE,
                Atom::Typeclass(_) => ATOM_TYPECLASS,
                Atom::Symbol(Symbol::True) => ATOM_TRUE,
                Atom::Symbol(Symbol::False) => ATOM_FALSE,
                Atom::Symbol(Symbol::Empty) => ATOM_SYMBOL_EMPTY,
                Atom::Symbol(Symbol::Bool) => ATOM_SYMBOL_BOOL,
                Atom::Symbol(Symbol::TypeSort) => ATOM_SYMBOL_TYPESORT,
                Atom::Symbol(Symbol::Type(_)) => ATOM_TYPE,
                Atom::Symbol(Symbol::GlobalConstant(_)) => ATOM_SYMBOL_GLOBAL,
                Atom::Symbol(Symbol::ScopedConstant(_)) => ATOM_SYMBOL_SCOPED,
                Atom::Symbol(Symbol::Synthetic(_)) => ATOM_SYMBOL_SYNTHETIC,
            },
        }
    }

    /// Appends the byte representation of this edge to the vector.
    /// Each edge is 3 bytes: discriminant + 2 bytes for ID (if applicable).
    pub fn append_to(&self, v: &mut Vec<u8>) {
        v.push(self.discriminant());
        let id: u16 = match self {
            Edge::Application | Edge::Arrow | Edge::LiteralForm(_) => 0,
            Edge::Atom(atom) => match atom {
                Atom::Variable(i) => *i,
                Atom::BoundVariable(i) => *i,
                Atom::True => 0,
                Atom::False => 0,
                Atom::Type0 => 0,
                Atom::Type(t) => t.as_u16(),
                Atom::Typeclass(tc) => tc.as_u16(),
                Atom::Symbol(Symbol::True) => 0,
                Atom::Symbol(Symbol::False) => 0,
                Atom::Symbol(Symbol::Empty) => 0,
                Atom::Symbol(Symbol::Bool) => 0,
                Atom::Symbol(Symbol::TypeSort) => 0,
                Atom::Symbol(Symbol::Type(t)) => t.as_u16(),
                Atom::Symbol(Symbol::GlobalConstant(c)) => *c,
                Atom::Symbol(Symbol::ScopedConstant(c)) => *c,
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
            LITERAL_POSITIVE => Edge::LiteralForm(true),
            LITERAL_NEGATIVE => Edge::LiteralForm(false),
            ATOM_VARIABLE => Edge::Atom(Atom::Variable(id)),
            ATOM_TRUE => Edge::Atom(Atom::True),
            ATOM_FALSE => Edge::Atom(Atom::False),
            ATOM_TYPE0 => Edge::Atom(Atom::Type0),
            ATOM_TYPE => Edge::Atom(Atom::Type(GroundTypeId::new(id))),
            ATOM_TYPECLASS => Edge::Atom(Atom::Typeclass(TypeclassId::new(id))),
            ATOM_SYMBOL_GLOBAL => Edge::Atom(Atom::Symbol(Symbol::GlobalConstant(id))),
            ATOM_SYMBOL_SCOPED => Edge::Atom(Atom::Symbol(Symbol::ScopedConstant(id))),
            ATOM_SYMBOL_SYNTHETIC => Edge::Atom(Atom::Symbol(Symbol::Synthetic(id))),
            ATOM_SYMBOL_EMPTY => Edge::Atom(Atom::Symbol(Symbol::Empty)),
            ATOM_SYMBOL_BOOL => Edge::Atom(Atom::Symbol(Symbol::Bool)),
            ATOM_SYMBOL_TYPESORT => Edge::Atom(Atom::Symbol(Symbol::TypeSort)),
            ATOM_BOUND_VARIABLE => Edge::Atom(Atom::BoundVariable(id)),
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

/// Encodes a type Term into the key buffer.
/// Uses the same structural encoding as terms, since types and terms share the same representation.
/// This handles both regular types (List[Int]) and dependent types (Fin[k] where k: Nat).
fn key_from_type(type_term: &Term, key: &mut Vec<u8>) {
    key_from_structure(type_term.as_ref(), key);
}

/// Unified structure encoding for both types and terms.
/// Substitute BoundVariable(0) with `arg` in `typ`, and decrement other bound variable indices.
/// This is used for computing the result type of a function application:
/// if f : Pi(A, B) and x : A, then f(x) : B[0 := x]
fn substitute_bound_zero(typ: &Term, arg: TermRef) -> Term {
    fn helper(typ: TermRef, arg: TermRef, depth: u16) -> Term {
        match typ.decompose() {
            Decomposition::Atom(KernelAtom::BoundVariable(i)) => {
                let i = *i;
                if i == depth {
                    // BoundVar(depth) at this level refers to the outermost Pi we're substituting
                    // Replace with arg
                    arg.to_owned()
                } else if i > depth {
                    // Refers to an outer binding, decrement since we're removing one binder
                    Term::atom(KernelAtom::BoundVariable(i - 1))
                } else {
                    // Refers to an inner binding, keep as is
                    Term::atom(KernelAtom::BoundVariable(i))
                }
            }
            Decomposition::Atom(atom) => Term::atom(atom.clone()),
            Decomposition::Application(func, arg_inner) => {
                let new_func = helper(func, arg, depth);
                let new_arg = helper(arg_inner, arg, depth);
                new_func.apply(&[new_arg])
            }
            Decomposition::Pi(input, output) => {
                let new_input = helper(input, arg, depth);
                // Inside the Pi body, depth increases by 1
                let new_output = helper(output, arg, depth + 1);
                Term::pi(new_input, new_output)
            }
        }
    }
    helper(typ.as_ref(), arg, 0)
}

/// Uses decomposition to handle all cases uniformly:
/// - Atoms: Variable, Symbol, Typeclass (with special handling for Type atoms)
/// - Applications: function + argument
/// - Pi types: encoded as Arrow + input + output
fn key_from_structure(term: TermRef, key: &mut Vec<u8>) {
    match term.decompose() {
        Decomposition::Atom(atom) => {
            let encoded_atom = match atom {
                KernelAtom::FreeVariable(i) => Atom::Variable(*i),
                KernelAtom::BoundVariable(i) => Atom::BoundVariable(*i),
                // Handle Type atoms specially to match expected encoding
                KernelAtom::Symbol(Symbol::Type(t)) => Atom::Type(*t),
                KernelAtom::Symbol(Symbol::True) => Atom::True,
                KernelAtom::Symbol(Symbol::False) => Atom::False,
                KernelAtom::Symbol(s) => Atom::Symbol(*s),
                KernelAtom::Typeclass(tc) => Atom::Typeclass(*tc),
            };
            Edge::Atom(encoded_atom).append_to(key);
        }
        Decomposition::Application(func, arg) => {
            Edge::Application.append_to(key);
            key_from_structure(func, key);
            key_from_structure(arg, key);
        }
        Decomposition::Pi(input, output) => {
            Edge::Arrow.append_to(key);
            key_from_structure(input, key);
            key_from_structure(output, key);
        }
    }
}

/// Writes the type of a term directly to the key buffer.
/// This is equivalent to:
///   let t = term.get_type_with_context(local_context, kernel_context);
///   key_from_type(&t, key);
/// But avoids the intermediate allocation.
fn key_from_term_type(
    term: TermRef,
    key: &mut Vec<u8>,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) {
    // Get the head's type (as a reference, no allocation)
    let head = term.get_head_atom();
    let head_type: &Term = match head {
        KernelAtom::FreeVariable(i) => {
            local_context.get_var_type(*i as usize).unwrap_or_else(|| {
                panic!(
                    "Variable x{} not found in LocalContext (size={})",
                    i,
                    local_context.len()
                )
            })
        }
        KernelAtom::Symbol(Symbol::True) | KernelAtom::Symbol(Symbol::False) => {
            // Special case: True/False has type Bool, encode it directly
            Edge::Atom(Atom::Symbol(Symbol::Bool)).append_to(key);
            return;
        }
        KernelAtom::BoundVariable(_) => {
            panic!("BoundVariable should not appear as term head in key_from_term_type")
        }
        KernelAtom::Symbol(Symbol::Type(_))
        | KernelAtom::Symbol(Symbol::Empty)
        | KernelAtom::Symbol(Symbol::Bool) => {
            // Types can appear as arguments to polymorphic functions.
            // Types have kind Type (TypeSort), so their "type" for the key is TypeSort.
            Edge::Atom(Atom::Symbol(Symbol::TypeSort)).append_to(key);
            return;
        }
        KernelAtom::Symbol(Symbol::TypeSort) => {
            // TypeSort is the kind of types. If it appears, it has kind TypeSort (or higher).
            // For now, just use TypeSort as its own kind.
            Edge::Atom(Atom::Symbol(Symbol::TypeSort)).append_to(key);
            return;
        }
        KernelAtom::Typeclass(_) => {
            panic!("Typeclass should not appear as term head in key_from_term_type")
        }
        KernelAtom::Symbol(symbol) => kernel_context.symbol_table.get_type(*symbol),
    };

    // Collect arguments and apply the type with proper substitution
    // For f(a)(b), we compute the type as: head_type[0 := a][0 := b]
    let args: Vec<TermRef> = term.iter_args().collect();

    // Apply the type for each argument, substituting bound variables
    let mut result_type = head_type.clone();
    for arg in &args {
        match result_type.as_ref().split_pi() {
            Some((_, output)) => {
                // Substitute BoundVar(0) in output with the actual argument
                // This handles dependent types properly
                result_type = substitute_bound_zero(&output.to_owned(), *arg);
            }
            None => panic!("Expected Pi type for function application"),
        }
    }

    // Now encode the result type
    key_from_type(&result_type, key);
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
    // Emit the result type of the term
    key_from_term_type(term, key, local_context, kernel_context);

    // Emit the structure of the term
    key_from_term_structure(term, key, local_context, kernel_context);
}

/// Encodes the structure of a term (without the result type prefix).
/// Used for recursive encoding of applications where the type is implicit.
fn key_from_term_structure(
    term: TermRef,
    key: &mut Vec<u8>,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) {
    match term.decompose() {
        Decomposition::Atom(head) => {
            let atom = match head {
                KernelAtom::FreeVariable(v) => Atom::Variable(*v),
                KernelAtom::BoundVariable(i) => Atom::BoundVariable(*i),
                KernelAtom::Symbol(Symbol::True) => Atom::True,
                KernelAtom::Symbol(Symbol::False) => Atom::False,
                KernelAtom::Symbol(Symbol::Type(t)) => Atom::Type(*t),
                KernelAtom::Typeclass(tc) => Atom::Typeclass(*tc),
                KernelAtom::Symbol(s) => Atom::Symbol(*s),
            };
            Edge::Atom(atom).append_to(key);
        }
        Decomposition::Application(func, arg) => {
            // Binary application: Application + domain type + func structure + arg full encoding
            Edge::Application.append_to(key);
            key_from_term_type(arg, key, local_context, kernel_context);
            // For func, we only emit structure (type is implicit from the Application)
            key_from_term_structure(func, key, local_context, kernel_context);
            // For arg, we emit the full encoding (type + structure)
            key_from_term_helper(arg, key, local_context, kernel_context);
        }
        Decomposition::Pi(_, _) => {
            // Pi types in pattern tree - not typically expected in term matching context
            panic!("Pi types should not appear in pattern tree term structure encoding");
        }
    }
}

/// Creates a key prefix for a term (currently empty).
pub fn term_key_prefix() -> Vec<u8> {
    Vec::new()
}

/// Generates a complete key for a term.
pub fn key_from_term(
    term: &Term,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Vec<u8> {
    let mut key = Vec::new();
    key_from_term_helper(term.as_ref(), &mut key, local_context, kernel_context);
    key
}

/// Generates a complete key for a term pair.
pub fn key_from_pair(
    term1: &Term,
    term2: &Term,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Vec<u8> {
    let mut key = Vec::new();
    key_from_term_type(term1.as_ref(), &mut key, local_context, kernel_context);
    key_from_term_helper(term1.as_ref(), &mut key, local_context, kernel_context);
    key_from_term_helper(term2.as_ref(), &mut key, local_context, kernel_context);
    key
}

/// Generates a complete key for a literal.
pub fn key_from_literal(
    literal: &Literal,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Vec<u8> {
    let mut key = Vec::new();
    Edge::LiteralForm(literal.positive).append_to(&mut key);
    key_from_term_type(
        literal.left.as_ref(),
        &mut key,
        local_context,
        kernel_context,
    );
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
        Edge::LiteralForm(literal.positive).append_to(&mut key);
        key_from_term_type(
            literal.left.as_ref(),
            &mut key,
            local_context,
            kernel_context,
        );
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

/// PatternTree: A pattern tree using curried representation and Term for type matching.
/// Supports type variables in patterns.
#[derive(Clone, Debug)]
pub struct PatternTree<T> {
    /// Maps byte keys to indices into the values vector.
    trie: Trie<Vec<u8>, usize>,

    /// Values stored in the tree.
    pub values: Vec<T>,
}

impl<T> PatternTree<T> {
    pub fn new() -> PatternTree<T> {
        PatternTree {
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
            500, // stack limit - need enough depth for complex nested terms
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
        let mut key = Vec::new();
        key_from_term_type(left.as_ref(), &mut key, local_context, kernel_context);
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

impl PatternTree<()> {
    /// Appends to the existing value if possible. Otherwise, inserts a vec![U].
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

/// The LiteralSet stores literals using a curried pattern tree.
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

/// Matches the function part of an application (without type prefix).
///
/// In the encoding, the function part of an application does NOT have its type emitted.
/// This function handles matching the function part:
/// 1. Try backreference (without type prefix)
/// 2. Try new variable (without type prefix)
/// 3. Structural match using decomposition
///
/// After matching func, it calls find_term_matches_while for the remaining terms
/// which DO get type prefixes.
fn match_func_part<'a, F>(
    subtrie: &SubTrie<Vec<u8>, usize>,
    key: &mut Vec<u8>,
    func: TermRef<'a>,
    rest_terms: &[TermRef<'a>],
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
        if stack_limit == 0 && !subtrie.is_empty() {
            eprintln!("WARNING: pattern_tree stack_limit exhausted in match_func_part - consider increasing the limit");
        }
        return true;
    }

    let initial_key_len = key.len();
    let head_atom = func.get_head_atom();

    // Case 1: func matches an existing replacement (backreference) - NO type prefix
    if !head_atom.is_variable() {
        for i in 0..replacements.len() {
            if func == replacements[i] {
                Edge::Atom(Atom::Variable(i as u16)).append_to(key);
                let new_subtrie = subtrie.subtrie(key as &[u8]);
                if !new_subtrie.is_empty() {
                    if !find_term_matches_while(
                        &new_subtrie,
                        key,
                        rest_terms,
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
            }
        }
    }

    // Case 2: func matches a new variable - NO type prefix
    if !head_atom.is_variable() {
        Edge::Atom(Atom::Variable(replacements.len() as u16)).append_to(key);
        let new_subtrie = subtrie.subtrie(key as &[u8]);
        if !new_subtrie.is_empty() {
            replacements.push(func);
            if !find_term_matches_while(
                &new_subtrie,
                key,
                rest_terms,
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

    // Case 3: structural match using decomposition - NO type prefix for func
    match func.decompose() {
        Decomposition::Atom(atom) => {
            // Atomic function: emit the atom directly (no type prefix)
            let edge_atom = match atom {
                KernelAtom::FreeVariable(v) => Atom::Variable(*v),
                KernelAtom::BoundVariable(i) => Atom::BoundVariable(*i),
                KernelAtom::Symbol(Symbol::True) => Atom::True,
                KernelAtom::Symbol(Symbol::False) => Atom::False,
                KernelAtom::Symbol(Symbol::Type(t)) => Atom::Type(*t),
                KernelAtom::Typeclass(tc) => Atom::Typeclass(*tc),
                KernelAtom::Symbol(s) => Atom::Symbol(*s),
            };
            Edge::Atom(edge_atom).append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);
            if !find_term_matches_while(
                &new_subtrie,
                key,
                rest_terms,
                local_context,
                kernel_context,
                stack_limit - 1,
                replacements,
                callback,
            ) {
                return false;
            }
        }
        Decomposition::Application(inner_func, inner_arg) => {
            // Nested application: func = inner_func(inner_arg)
            // Encoding: Application + domain_type + inner_func_encoding + inner_arg_encoding
            Edge::Application.append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);

            key_from_term_type(inner_arg, key, local_context, kernel_context);
            let new_subtrie2 = new_subtrie.subtrie(key as &[u8]);

            // Build rest: [inner_arg, ...rest_terms]
            let mut arg_and_rest: Vec<TermRef<'a>> = Vec::with_capacity(1 + rest_terms.len());
            arg_and_rest.push(inner_arg);
            arg_and_rest.extend_from_slice(rest_terms);

            // Match inner_func (without type) then arg_and_rest (with type)
            if !match_func_part(
                &new_subtrie2,
                key,
                inner_func,
                &arg_and_rest,
                local_context,
                kernel_context,
                stack_limit - 1,
                replacements,
                callback,
            ) {
                return false;
            }
        }
        Decomposition::Pi(_, _) => {
            // Pi types should not appear in pattern matching context
            panic!("Pi types should not appear in pattern tree matching");
        }
    }

    key.truncate(initial_key_len);
    true
}

/// Matches a sequence of terms against patterns in the trie.
///
/// Uses decomposition to handle curried application structure uniformly.
/// For any term, we try three cases:
/// 1. Match the whole term against an existing replacement (backreference)
/// 2. Match the whole term against a new pattern variable
/// 3. Match the structure (atom or decomposed application)
///
/// The decomposition approach naturally handles partial applications because
/// f(a, b) decomposes to (f(a), b), and when we recursively match f(a),
/// it can be matched against a pattern variable or further decomposed.
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
        eprintln!("WARNING: pattern_tree stack_limit exhausted in find_term_matches_while - consider increasing the limit");
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
            key_from_term_type(first, key, local_context, kernel_context);
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
    key_from_term_type(first, key, local_context, kernel_context);
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

    // Case 3: structural match using decomposition
    // Skip if head is a variable (variables in query must match via Cases 1 or 2)
    let head_atom = first.get_head_atom();
    if head_atom.is_variable() {
        return true;
    }

    // Emit the result type
    key_from_term_type(first, key, local_context, kernel_context);

    match first.decompose() {
        Decomposition::Atom(atom) => {
            // Atomic term: match the atom directly
            let edge_atom = match atom {
                KernelAtom::FreeVariable(v) => Atom::Variable(*v),
                KernelAtom::BoundVariable(i) => Atom::BoundVariable(*i),
                KernelAtom::Symbol(Symbol::True) => Atom::True,
                KernelAtom::Symbol(Symbol::False) => Atom::False,
                KernelAtom::Symbol(Symbol::Type(t)) => Atom::Type(*t),
                KernelAtom::Typeclass(tc) => Atom::Typeclass(*tc),
                KernelAtom::Symbol(s) => Atom::Symbol(*s),
            };
            Edge::Atom(edge_atom).append_to(key);
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
        Decomposition::Application(func, arg) => {
            // Application term: decompose into (func, arg)
            // Encoding: result_type + Application + domain_type + func_encoding + arg_encoding
            // Note: func_encoding has NO type prefix, arg_encoding HAS type prefix

            // Emit Application edge
            Edge::Application.append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);

            // Emit domain type of the argument
            key_from_term_type(arg, key, local_context, kernel_context);
            let new_subtrie2 = new_subtrie.subtrie(key as &[u8]);

            // Build rest terms: [arg, ...rest]
            let mut arg_and_rest: Vec<TermRef<'a>> = Vec::with_capacity(1 + rest.len());
            arg_and_rest.push(arg);
            arg_and_rest.extend_from_slice(rest);

            // Match func (without type prefix) then arg_and_rest (with type prefix)
            if !match_func_part(
                &new_subtrie2,
                key,
                func,
                &arg_and_rest,
                local_context,
                kernel_context,
                stack_limit - 1,
                replacements,
                callback,
            ) {
                return false;
            }
        }
        Decomposition::Pi(_, _) => {
            panic!("Pi types should not appear in pattern tree matching");
        }
    }

    key.truncate(initial_key_len);
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_edge_roundtrip() {
        let edges = vec![
            Edge::Application,
            Edge::Arrow,
            Edge::LiteralForm(true),
            Edge::LiteralForm(false),
            Edge::Atom(Atom::Variable(0)),
            Edge::Atom(Atom::Variable(42)),
            Edge::Atom(Atom::True),
            Edge::Atom(Atom::False),
            Edge::Atom(Atom::Type0),
            Edge::Atom(Atom::Type(GroundTypeId::new(1))),
            Edge::Atom(Atom::Type(GroundTypeId::new(100))),
            Edge::Atom(Atom::Typeclass(TypeclassId::new(5))),
            Edge::Atom(Atom::Symbol(Symbol::GlobalConstant(10))),
            Edge::Atom(Atom::Symbol(Symbol::ScopedConstant(20))),
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
        Edge::LiteralForm(true).append_to(&mut bytes);
        Edge::Atom(Atom::Type(GroundTypeId::new(1))).append_to(&mut bytes);
        Edge::Atom(Atom::Symbol(Symbol::ScopedConstant(5))).append_to(&mut bytes);

        let debug = Edge::debug_bytes(&bytes);
        assert!(debug.contains("LiteralForm"));
        assert!(debug.contains("Type"));
        assert!(debug.contains("ScopedConstant"));
    }

    #[test]
    fn test_key_from_ground_type() {
        // Test encoding of the Bool type (now a Symbol variant)
        let bool_type = Term::bool_type();
        let mut key = Vec::new();
        key_from_type(&bool_type, &mut key);

        // Should be just Atom(Symbol(Bool))
        assert_eq!(key.len(), 3);
        let edge = Edge::from_bytes(key[0], key[1], key[2]);
        assert_eq!(edge, Edge::Atom(Atom::Symbol(Symbol::Bool)));
    }

    #[test]
    fn test_key_from_type_arrow() {
        // Test encoding of Bool -> Bool
        let bool_type = Term::bool_type();
        let arrow_type = Term::pi(bool_type.clone(), bool_type.clone());
        let mut key = Vec::new();
        key_from_type(&arrow_type, &mut key);

        // Should be: Arrow + Atom(Symbol(Bool)) + Atom(Symbol(Bool))
        assert_eq!(key.len(), 9);

        let edge1 = Edge::from_bytes(key[0], key[1], key[2]);
        assert_eq!(edge1, Edge::Arrow);

        let edge2 = Edge::from_bytes(key[3], key[4], key[5]);
        assert_eq!(edge2, Edge::Atom(Atom::Symbol(Symbol::Bool)));

        let edge3 = Edge::from_bytes(key[6], key[7], key[8]);
        assert_eq!(edge3, Edge::Atom(Atom::Symbol(Symbol::Bool)));
    }

    #[test]
    fn test_key_from_term_atomic() {
        // Test encoding of an atomic term c0 : Bool
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2", "c3", "c4"], "Bool");
        let lctx = kctx.parse_local(&["Bool", "Bool"]);

        let term = Term::parse("c0");
        let key = key_from_term(&term, &lctx, &kctx);

        // For an atomic term: type + atom
        // So: Symbol(Bool) + Atom(c0)
        let debug = Edge::debug_bytes(&key);
        assert!(debug.contains("Bool"), "key: {}", debug);
        assert!(debug.contains("ScopedConstant"), "key: {}", debug);
    }

    #[test]
    fn test_key_from_literal() {
        // Test encoding of x0 = c0
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2", "c3", "c4"], "Bool");

        let clause = kctx.parse_clause("x0 = c0", &["Bool"]);
        let literal = &clause.literals[0];
        let key = key_from_literal(literal, clause.get_local_context(), &kctx);

        // Should start with LiteralForm(true) since it's positive
        let edge1 = Edge::from_bytes(key[0], key[1], key[2]);
        assert_eq!(edge1, Edge::LiteralForm(true));

        // Should contain the type and both terms
        let debug = Edge::debug_bytes(&key);
        assert!(debug.contains("LiteralForm(true)"), "key: {}", debug);
    }

    #[test]
    fn test_pattern_tree_insert_term() {
        // Test inserting and finding atomic terms
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2", "c3", "c4"], "Bool");
        let lctx = kctx.parse_local(&[]);

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Insert c0
        let term = Term::parse("c0");
        tree.insert_term(&term, 42, &lctx, &kctx);

        assert_eq!(tree.values.len(), 1);
        assert_eq!(tree.values[0], 42);
    }

    #[test]
    fn test_pattern_tree_insert_pair() {
        // Test inserting term pairs
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2", "c3", "c4"], "Bool");
        let lctx = kctx.parse_local(&[]);

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Insert (c0, c1)
        let term1 = Term::parse("c0");
        let term2 = Term::parse("c1");
        tree.insert_pair(&term1, &term2, 99, &lctx, &kctx);

        assert_eq!(tree.values.len(), 1);
        assert_eq!(tree.values[0], 99);

        // Should find the pair
        let found = tree.find_pair(&term1, &term2, &lctx, &kctx);
        assert_eq!(found, Some(&99));

        // Should not find a different pair
        let term3 = Term::parse("c2");
        let not_found = tree.find_pair(&term1, &term3, &lctx, &kctx);
        assert_eq!(not_found, None);
    }

    #[test]
    fn test_pattern_tree_variable_matching() {
        // Test that patterns with variables match concrete terms
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2", "c3", "c4"], "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Insert pattern "x0 = c0" - a variable equals a constant
        let pattern_left = Term::parse("x0");
        let pattern_right = Term::parse("c0");
        tree.insert_pair(&pattern_left, &pattern_right, 7, &lctx, &kctx);

        // Query "c1 = c0" should match (c1 can be matched by variable x0)
        let query_lctx = kctx.parse_local(&[]);
        let query_left = Term::parse("c1");
        let query_right = Term::parse("c0");
        let found = tree.find_pair(&query_left, &query_right, &query_lctx, &kctx);
        assert_eq!(found, Some(&7));
    }

    #[test]
    fn test_pattern_tree_application_with_variable() {
        // Test that patterns with function applications and variables match correctly
        // c1 : Bool -> Bool, so c1(x0) : Bool when x0 : Bool
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c5", "c6"], "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Insert pattern "c1(x0) = c5" - a function applied to a variable equals a constant
        let pattern_left = Term::parse("c1(x0)");
        let pattern_right = Term::parse("c5");
        tree.insert_pair(&pattern_left, &pattern_right, 42, &lctx, &kctx);

        // Query "c1(c6) = c5" should match (c6 : Bool can be matched by variable x0)
        let query_lctx = kctx.parse_local(&[]);
        let query_left = Term::parse("c1(c6)");
        let query_right = Term::parse("c5");
        let found = tree.find_pair(&query_left, &query_right, &query_lctx, &kctx);
        assert_eq!(found, Some(&42));
    }

    #[test]
    fn test_pattern_tree_clause_with_function_application() {
        // Test that clauses with function applications can be inserted and found
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c1", "Bool -> Bool")
            .parse_constant("c5", "Bool");

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Create a clause with a function application: c1(x0) = c5
        let clause = kctx.parse_clause("c1(x0) = c5", &["Bool"]);
        tree.insert_clause(&clause, 42, &kctx);

        // Should be able to find the exact same clause
        let found = tree.find_clause(&clause, &kctx);
        assert_eq!(found, Some(&42));
    }

    #[test]
    fn test_pattern_tree_clause_specialization() {
        // Test that find_clause can match a specialized clause against a pattern.
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c5", "Bool");

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Insert pattern: x0 = x0
        let clause = kctx.parse_clause("x0 = x0", &["Bool"]);
        tree.insert_clause(&clause, 42, &kctx);

        // Query: c5 = c5 should match (c5 substituted for x0)
        let special = kctx.parse_clause("c5 = c5", &[]);
        let found_special = tree.find_clause(&special, &kctx);
        assert_eq!(found_special, Some(&42));
    }

    #[test]
    fn test_pattern_tree_clause_multi_literal() {
        // Test clause with multiple literals containing function applications
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c5", "c6"], "Bool");

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Create a clause with two literals: c1(x0) = c5 or c0(x0, x1) = c6
        let clause = kctx.parse_clause("c1(x0) = c5 or c0(x0, x1) = c6", &["Bool", "Bool"]);
        tree.insert_clause(&clause, 99, &kctx);

        // Should be able to find the clause
        let found = tree.find_clause(&clause, &kctx);
        assert_eq!(found, Some(&99));
    }

    #[test]
    fn test_insert_or_append_and_find() {
        // Test the insert_or_append + find_term_matches_while pattern used by RewriteTree
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2"], "Bool");
        let lctx = kctx.parse_local(&[]);

        let mut tree: PatternTree<Vec<usize>> = PatternTree::new();

        // Insert c1 using insert_or_append (like RewriteTree does)
        let term = Term::parse("c1");
        PatternTree::insert_or_append(&mut tree, &term, 42, &lctx, &kctx);

        // Now try to find it using the pattern that RewriteTree uses
        let mut key = term_key_prefix();

        let terms = [term.as_ref()];
        let mut replacements: Vec<TermRef> = vec![];
        let mut found_id = None;

        tree.find_term_matches_while(
            &mut key,
            &terms,
            &lctx,
            &kctx,
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
        // Test that the pattern tree can match a partial application against a function variable.
        // This is a key capability of curried representation.
        //
        // c0 : (Bool, Bool) -> Bool (2-arg function)
        // c1 : Bool -> Bool (1-arg function)
        // c5, c6 : Bool
        //
        // Pattern: x0(c6) where x0 : Bool -> Bool
        // Query: c0(c5, c6) = ((Bool, Bool) -> Bool)(Bool, Bool) = Bool
        //
        // In curried form:
        // - c0(c5, c6) becomes Application(Application(c0, c5), c6)
        // - x0(c6) becomes Application(x0, c6)
        //
        // The match should succeed with x0 = c0(c5), which has type Bool -> Bool.
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c5", "c6"], "Bool");

        // x0: Bool -> Bool
        let lctx = kctx.parse_local(&["Bool -> Bool"]);

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Insert pattern: x0(c6) = c5
        let pattern_left = Term::parse("x0(c6)");
        let pattern_right = Term::parse("c5");
        tree.insert_pair(&pattern_left, &pattern_right, 42, &lctx, &kctx);

        // First verify that the partial application c0(c5) has type Bool -> Bool
        let partial_app = Term::parse("c0(c5)");
        let partial_type = partial_app.get_type_with_context(&lctx, &kctx);
        let x0_type = lctx.get_var_type(0);
        assert_eq!(
            partial_type,
            *x0_type.unwrap(),
            "c0(c5) should have the same type as x0 (Bool -> Bool)"
        );

        // Query: c0(c5, c6) = c5
        // c0(c5) is a partial application of type Bool -> Bool, which should match x0
        let query_left = Term::parse("c0(c5, c6)");
        let query_right = Term::parse("c5");
        let found = tree.find_pair(&query_left, &query_right, &lctx, &kctx);

        // The pattern tree should find this match because:
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
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c5", "c6", "c7"], "Bool");

        let lctx = kctx.parse_local(&["Bool -> Bool"]);

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Insert pattern: x0(c5) = c6
        let pattern_left = Term::parse("x0(c5)");
        let pattern_right = Term::parse("c6");
        tree.insert_pair(&pattern_left, &pattern_right, 100, &lctx, &kctx);

        // First verify c1 has type Bool -> Bool
        let c1_term = Term::parse("c1");
        let c1_type = c1_term.get_type_with_context(&lctx, &kctx);
        let x0_type = lctx.get_var_type(0);
        assert_eq!(
            c1_type,
            *x0_type.unwrap(),
            "c1 should have the same type as x0 (Bool -> Bool)"
        );

        // Query 1: c1(c5) = c6 - same arity, should match with x0 = c1
        let query1_left = Term::parse("c1(c5)");
        let query1_right = Term::parse("c6");
        let found1 = tree.find_pair(&query1_left, &query1_right, &lctx, &kctx);
        assert_eq!(found1, Some(&100), "Same-arity application should match");

        // Query 2: c0(c7, c5) = c6 - different arity, but c0(c7) has type Bool -> Bool
        // So c0(c7, c5) = Application(Application(c0, c7), c5) should match x0(c5)
        // with x0 = c0(c7)
        let query2_left = Term::parse("c0(c7, c5)");
        let query2_right = Term::parse("c6");
        let found2 = tree.find_pair(&query2_left, &query2_right, &lctx, &kctx);
        assert_eq!(
            found2,
            Some(&100),
            "Different-arity application should match via currying"
        );
    }

    #[test]
    fn test_clause_with_repeated_applied_variable() {
        // Test that a variable used in function position appearing in multiple literals
        // is correctly matched via backreference.
        //
        // Pattern: not x0(c5) or x0(x1)
        //   where x0: Bool -> Bool, x1: Bool, c5: Bool
        //
        // Query: not c1(c5) or c1(c6)
        //   where c1: Bool -> Bool, c5, c6: Bool
        //
        // This should match with x0 -> c1, x1 -> c6
        let mut kctx = KernelContext::new();
        // Add constants in order so Term::parse indices match
        kctx.parse_constant("c0", "Bool") // placeholder
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c2", "c3", "c4"], "Bool") // placeholders
            .parse_constants(&["c5", "c6"], "Bool");

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Insert pattern: not x0(c5) or x0(x1), where x0: Bool -> Bool, x1: Bool
        let pattern = kctx.parse_clause("not x0(c5) or x0(x1)", &["Bool -> Bool", "Bool"]);
        tree.insert_clause(&pattern, 42, &kctx);

        // Query: not c1(c5) or c1(c6)
        let query = kctx.parse_clause("not c1(c5) or c1(c6)", &[]);

        // This should find the pattern with x0 -> c1, x1 -> c6
        let found = tree.find_clause(&query, &kctx);
        assert_eq!(
            found,
            Some(&42),
            "Should match clause with repeated applied variable"
        );
    }

    #[test]
    fn test_pair_with_applied_variable_in_args() {
        // Simpler test: just a term pair (single literal), not a full clause
        //
        // Pattern: x0(c1(x0)) = c5
        //   where x0: Bool -> Bool, c1: Bool -> Bool, c5: Bool
        //
        // Query: c0(c6, c1(c0(c6))) = c5
        //   where c0: (Bool, Bool) -> Bool, c6: Bool
        //
        // This should match with x0 -> c0(c6)
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c5", "c6"], "Bool");

        // x0: Bool -> Bool
        let lctx = kctx.parse_local(&["Bool -> Bool"]);

        let mut tree: PatternTree<usize> = PatternTree::new();

        // Insert pattern: x0(c1(x0)) = c5
        let pattern_left = Term::parse("x0(c1(x0))");
        let pattern_right = Term::parse("c5");
        tree.insert_pair(&pattern_left, &pattern_right, 42, &lctx, &kctx);

        // Query: c0(c6, c1(c0(c6))) = c5
        let query_lctx = kctx.parse_local(&[]);
        let query_left = Term::parse("c0(c6, c1(c0(c6)))");
        let query_right = Term::parse("c5");
        let found = tree.find_pair(&query_left, &query_right, &query_lctx, &kctx);

        assert_eq!(
            found,
            Some(&42),
            "Should match pair where applied variable also appears as argument"
        );
    }

    #[test]
    fn test_key_from_type_variable() {
        // Type variable T0 should encode as Variable(0)
        let type_var = Term::atom(KernelAtom::FreeVariable(0));
        let mut key = Vec::new();
        key_from_type(&type_var, &mut key);
        assert_eq!(key.len(), 3);
        let edge = Edge::from_bytes(key[0], key[1], key[2]);
        assert_eq!(edge, Edge::Atom(Atom::Variable(0)));
    }

    #[test]
    fn test_key_from_type_variable_higher_id() {
        // Type variable T5 should encode as Variable(5)
        let type_var = Term::atom(KernelAtom::FreeVariable(5));
        let mut key = Vec::new();
        key_from_type(&type_var, &mut key);
        assert_eq!(key.len(), 3);
        let edge = Edge::from_bytes(key[0], key[1], key[2]);
        assert_eq!(edge, Edge::Atom(Atom::Variable(5)));
    }

    #[test]
    fn test_key_from_parameterized_type_with_variable() {
        // List[T0] should encode as: Application + Type(List) + Variable(0)
        let mut kctx = KernelContext::new();
        kctx.parse_type_constructor("List", 1);

        let list_t0 = kctx.parse_type("List[T0]");
        let mut key = Vec::new();
        key_from_type(&list_t0, &mut key);

        // Verify structure: Application + Type(List) + Variable(0)
        let debug = Edge::debug_bytes(&key);
        assert!(debug.contains("Application"), "key: {}", debug);
        assert!(debug.contains("Type("), "key: {}", debug);
        assert!(debug.contains("Variable(0)"), "key: {}", debug);
    }

    #[test]
    fn test_key_from_arrow_type_with_variables() {
        // T0 -> T1 should encode as: Arrow + Variable(0) + Variable(1)
        let kctx = KernelContext::new();
        let arrow_type = kctx.parse_type("T0 -> T1");

        let mut key = Vec::new();
        key_from_type(&arrow_type, &mut key);

        // Verify structure: Arrow + Variable(0) + Variable(1)
        let debug = Edge::debug_bytes(&key);
        assert!(debug.contains("Arrow"), "key: {}", debug);
        assert!(debug.contains("Variable(0)"), "key: {}", debug);
        assert!(debug.contains("Variable(1)"), "key: {}", debug);
    }

    #[test]
    fn test_pattern_tree_with_type_variable() {
        // Test that type variables in the type encoding are correctly encoded and matched.
        // This test verifies the key encoding produces matching keys for identical type structures.
        let kctx = KernelContext::new();

        // Create LocalContext: x0 : Type, x1 : x0 (x1 has a type variable as its type)
        let lctx = LocalContext::from_types(vec![
            Term::type_sort(),
            Term::parse("x0"), // x1's type is x0, a type variable
        ]);

        // Generate keys for the same pattern twice
        let x1 = Term::parse("x1");
        let key1 = key_from_term(&x1, &lctx, &kctx);
        let key2 = key_from_term(&x1, &lctx, &kctx);

        // Keys should be identical
        assert_eq!(key1, key2, "Keys for identical patterns should match");

        // Verify the key structure contains the type variable encoding
        let debug = Edge::debug_bytes(&key1);
        assert!(
            debug.contains("Variable(0)"),
            "Key should contain type variable: {}",
            debug
        );
        assert!(
            debug.contains("Variable(1)"),
            "Key should contain term variable: {}",
            debug
        );
    }

    #[test]
    fn test_key_from_type_typeclass() {
        // Typeclass constraint should encode as Atom(Typeclass(id))
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Monoid");
        let monoid_id = kctx.type_store.get_typeclass_id_by_name("Monoid").unwrap();

        // Create a type term for the typeclass
        let typeclass_type = Term::typeclass(monoid_id);
        let mut key = Vec::new();
        key_from_type(&typeclass_type, &mut key);

        // Should be Atom(Typeclass(monoid_id))
        assert_eq!(key.len(), 3);
        let edge = Edge::from_bytes(key[0], key[1], key[2]);
        assert_eq!(edge, Edge::Atom(Atom::Typeclass(monoid_id)));
    }

    #[test]
    fn test_pattern_tree_with_typeclass_constraint() {
        // Test that a term with typeclass-constrained type encodes correctly
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Monoid");
        let monoid_id = kctx.type_store.get_typeclass_id_by_name("Monoid").unwrap();

        // Create LocalContext: x0 has type Monoid (typeclass constraint)
        let typeclass_type = Term::typeclass(monoid_id);
        let lctx = LocalContext::from_types(vec![typeclass_type.clone()]);

        // Generate key for x0 which has typeclass constraint
        let x0 = Term::parse("x0");
        let key = key_from_term(&x0, &lctx, &kctx);

        // Verify the key contains the typeclass encoding
        let debug = Edge::debug_bytes(&key);
        assert!(
            debug.contains("Typeclass"),
            "Key should contain typeclass type: {}",
            debug
        );
        assert!(
            debug.contains("Variable(0)"),
            "Key should contain term variable: {}",
            debug
        );
    }

    #[test]
    fn test_key_from_type_dependent() {
        // Test: Fin[c0] where c0: Nat encodes correctly (dependent type)
        let mut kctx = KernelContext::new();
        kctx.parse_type_constructor("Fin", 1);
        kctx.parse_datatype("Nat");

        let nat_id = kctx.type_store.get_ground_id_by_name("Nat").unwrap();
        let nat_type = Term::ground_type(nat_id);
        let fin_id = kctx.type_store.get_ground_id_by_name("Fin").unwrap();

        // c0: Nat (a value, not a type)
        kctx.symbol_table.add_scoped_constant(nat_type.clone());

        // Fin[c0] - a dependent type where c0 is a Nat value
        let c0 = Term::parse("c0");
        let fin_c0 = Term::new(KernelAtom::Symbol(Symbol::Type(fin_id)), vec![c0]);

        let mut key = Vec::new();
        key_from_type(&fin_c0, &mut key);

        // Should not panic, and should produce a valid encoding
        let debug = Edge::debug_bytes(&key);
        assert!(
            debug.contains("Application"),
            "Dependent type should encode as application: {}",
            debug
        );
        assert!(
            debug.contains("ScopedConstant(0)"),
            "Should contain the value argument c0: {}",
            debug
        );
    }

    #[test]
    fn test_key_from_type_dependent_with_variable() {
        // Test: Fin[x0] where x0: Nat encodes correctly
        let mut kctx = KernelContext::new();
        kctx.parse_type_constructor("Fin", 1);
        kctx.parse_datatype("Nat");

        let _nat_id = kctx.type_store.get_ground_id_by_name("Nat").unwrap();
        let fin_id = kctx.type_store.get_ground_id_by_name("Fin").unwrap();

        // Fin[x0] where x0 is a variable of type Nat
        let x0 = Term::atom(KernelAtom::FreeVariable(0));
        let fin_x0 = Term::new(KernelAtom::Symbol(Symbol::Type(fin_id)), vec![x0]);

        let mut key = Vec::new();
        key_from_type(&fin_x0, &mut key);

        // Should not panic, and should produce a valid encoding
        let debug = Edge::debug_bytes(&key);
        assert!(
            debug.contains("Application"),
            "Dependent type should encode as application: {}",
            debug
        );
        assert!(
            debug.contains("Variable(0)"),
            "Should contain the variable argument x0: {}",
            debug
        );
    }

    #[test]
    fn test_pattern_tree_with_dependent_type() {
        // Test pattern tree insert with terms that have dependent types
        // e.g., a function f : Fin[n] -> Bool where n : Nat

        let mut kctx = KernelContext::new();
        kctx.parse_type_constructor("Fin", 1);
        kctx.parse_datatype("Nat");

        let nat_id = kctx.type_store.get_ground_id_by_name("Nat").unwrap();
        let nat_type = Term::ground_type(nat_id);
        let fin_id = kctx.type_store.get_ground_id_by_name("Fin").unwrap();

        // c0 : Nat (a value parameter for Fin)
        kctx.symbol_table.add_scoped_constant(nat_type.clone());

        // Fin[c0] - the dependent type
        let c0 = Term::atom(KernelAtom::Symbol(Symbol::ScopedConstant(0)));
        let fin_c0 = Term::new(KernelAtom::Symbol(Symbol::Type(fin_id)), vec![c0.clone()]);

        // c1 : Fin[c0] (a value of the dependent type)
        kctx.symbol_table.add_scoped_constant(fin_c0.clone());

        // LocalContext: x0 : Nat, x1 : Fin[x0]
        let x0_type_var = Term::atom(KernelAtom::FreeVariable(0));
        let fin_x0 = Term::new(KernelAtom::Symbol(Symbol::Type(fin_id)), vec![x0_type_var]);
        let lctx = LocalContext::from_types(vec![nat_type.clone(), fin_x0.clone()]);

        // Create terms: x1 (variable of dependent type) and c1 (constant of dependent type)
        let x1 = Term::atom(KernelAtom::FreeVariable(1));
        let c1 = Term::atom(KernelAtom::Symbol(Symbol::ScopedConstant(1)));

        // Generate keys - both should work without panicking
        let key_x1 = key_from_term(&x1, &lctx, &kctx);
        let key_c1 = key_from_term(&c1, &LocalContext::empty(), &kctx);

        // Verify keys contain expected structure
        let debug_x1 = Edge::debug_bytes(&key_x1);
        let debug_c1 = Edge::debug_bytes(&key_c1);

        // Both should encode the Fin type application
        assert!(
            debug_x1.contains("Application"),
            "x1's type should be encoded as application: {}",
            debug_x1
        );
        assert!(
            debug_c1.contains("Application"),
            "c1's type should be encoded as application: {}",
            debug_c1
        );

        // Test actual pattern tree insertion - should not panic
        let mut tree: PatternTree<usize> = PatternTree::new();

        // Insert x1 (has dependent type Fin[x0])
        tree.insert_term(&x1, 1, &lctx, &kctx);

        // Insert c1 (has dependent type Fin[c0])
        tree.insert_term(&c1, 2, &LocalContext::empty(), &kctx);

        // Verify both were inserted
        assert_eq!(tree.values.len(), 2, "Both terms should be in the tree");
        assert_eq!(tree.values[0], 1);
        assert_eq!(tree.values[1], 2);
    }

    #[test]
    fn test_key_from_dependent_pi_type() {
        // Test: Π(R: Ring), R -> R -> R encodes correctly
        // This is the type of a polymorphic function like `add`
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Ring");

        let dependent_pi = kctx.parse_dependent_type(&["Ring"], "T0 -> T0 -> T0");

        let mut key = Vec::new();
        key_from_type(&dependent_pi, &mut key);

        // Should not panic, and should produce a valid encoding
        let debug = Edge::debug_bytes(&key);

        // Should contain Arrow edges for the Pi types
        assert!(
            debug.contains("Arrow"),
            "Dependent Pi type should encode with Arrow: {}",
            debug
        );

        // Should contain BoundVariable(0) for the bound type variable
        assert!(
            debug.contains("BoundVariable(0)"),
            "Should contain bound variable b0: {}",
            debug
        );
    }

    #[test]
    fn test_key_from_nested_dependent_pi() {
        // Test: Π(R: Ring), Π(n: Nat), Matrix[R, n, n]
        // More complex dependent type with multiple binders
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Ring");
        kctx.parse_datatype("Nat");
        kctx.parse_type_constructor("Matrix", 3);

        let nested_pi = kctx.parse_dependent_type(&["Ring", "Nat"], "Matrix[T0, T1, T1]");

        let mut key = Vec::new();
        key_from_type(&nested_pi, &mut key);

        let debug = Edge::debug_bytes(&key);

        // Should contain both BoundVariable(0) and BoundVariable(1)
        assert!(
            debug.contains("BoundVariable(0)"),
            "Should contain b0: {}",
            debug
        );
        assert!(
            debug.contains("BoundVariable(1)"),
            "Should contain b1: {}",
            debug
        );
    }

    #[test]
    fn test_pattern_tree_with_dependent_pi_function_type() {
        // Test pattern tree insertion for a function whose type is a dependent Pi type
        // e.g., `add : Π(R: Ring), R -> R -> R`
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Ring");

        // Create the dependent Pi type: Π(R: Ring), R -> R -> R
        let add_type = kctx.parse_dependent_type(&["Ring"], "T0 -> T0 -> T0");

        // Create constant `add` with this type
        kctx.symbol_table.add_scoped_constant(add_type.clone());

        // Create term: c0 (the `add` function)
        let add_term = Term::atom(KernelAtom::Symbol(Symbol::ScopedConstant(0)));

        // Generate key - should not panic
        let key = key_from_term(&add_term, &LocalContext::empty(), &kctx);

        // Verify key contains expected structure
        let debug = Edge::debug_bytes(&key);
        assert!(
            debug.contains("Arrow"),
            "add's type should encode with Arrow: {}",
            debug
        );
        assert!(
            debug.contains("BoundVariable(0)"),
            "add's type should contain b0: {}",
            debug
        );

        // Test actual pattern tree insertion
        let mut tree: PatternTree<usize> = PatternTree::new();
        tree.insert_term(&add_term, 1, &LocalContext::empty(), &kctx);

        // Verify insertion
        assert_eq!(tree.values.len(), 1, "add should be in the tree");
        assert_eq!(tree.values[0], 1);
    }

    #[test]
    fn test_pattern_tree_match_dependent_pi_functions() {
        // Test that two functions with the same dependent Pi type structure
        // can be found in the pattern tree
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Ring");

        // Create the dependent Pi type: Π(R: Ring), R -> R -> R
        let op_type = kctx.parse_dependent_type(&["Ring"], "T0 -> T0 -> T0");

        // Create two constants with this type: c0 = add, c1 = mul
        kctx.symbol_table.add_scoped_constant(op_type.clone());
        kctx.symbol_table.add_scoped_constant(op_type.clone());

        let add_term = Term::atom(KernelAtom::Symbol(Symbol::ScopedConstant(0)));
        let mul_term = Term::atom(KernelAtom::Symbol(Symbol::ScopedConstant(1)));

        // Insert both into the pattern tree
        let mut tree: PatternTree<&str> = PatternTree::new();
        tree.insert_term(&add_term, "add", &LocalContext::empty(), &kctx);
        tree.insert_term(&mul_term, "mul", &LocalContext::empty(), &kctx);

        // Verify both were inserted
        assert_eq!(tree.values.len(), 2, "Both ops should be in the tree");

        // Both should have the same type encoding (up to the head atom)
        let key_add = key_from_term(&add_term, &LocalContext::empty(), &kctx);
        let key_mul = key_from_term(&mul_term, &LocalContext::empty(), &kctx);

        // The keys differ only in the head atom (c0 vs c1), but the type portion should be identical
        // Both start with the head atom, then the type encoding follows
        let debug_add = Edge::debug_bytes(&key_add);
        let debug_mul = Edge::debug_bytes(&key_mul);

        // Both should have the same Arrow and BoundVariable structure
        assert!(debug_add.contains("Arrow") && debug_mul.contains("Arrow"));
        assert!(debug_add.contains("BoundVariable(0)") && debug_mul.contains("BoundVariable(0)"));
    }

    #[test]
    fn test_polymorphic_clause_matching() {
        // Test: Pattern is `add[R](x, y) = add[R](y, x)` for any R: Ring
        // Query is `add[Int](c, f(d)) = add[Int](f(d), c)` where Int: Ring
        // The query should match the pattern.

        let mut kctx = KernelContext::new();

        // Register Ring typeclass and mark Int as implementing Ring
        kctx.parse_typeclass("Ring").parse_instance("Int", "Ring");

        // Create `add` with polymorphic type: Π(R: Ring). R -> R -> R
        kctx.parse_polymorphic_constant("c0", &["Ring"], "T0 -> T0 -> T0"); // add

        // Create constants for the query
        kctx.parse_constant("c1", "Int -> Int"); // f
        kctx.parse_constants(&["c2", "c3"], "Int"); // c, d

        // Pattern clause: add[R](x, y) = add[R](y, x)
        // x0: Ring (type variable R), x1: x0 (value x), x2: x0 (value y)
        let pattern_clause =
            kctx.parse_clause("c0(x0, x1, x2) = c0(x0, x2, x1)", &["Ring", "x0", "x0"]);

        // Insert pattern into tree
        let mut tree: PatternTree<&str> = PatternTree::new();
        tree.insert_clause(&pattern_clause, "commutativity", &kctx);

        // Query clause: add[Int](c, f(d)) = add[Int](f(d), c)
        let query_clause = kctx.parse_clause("c0(Int, c2, c1(c3)) = c0(Int, c1(c3), c2)", &[]);

        // Try to find the pattern
        let found = tree.find_clause(&query_clause, &kctx);

        assert_eq!(
            found,
            Some(&"commutativity"),
            "Query should match the polymorphic commutativity pattern"
        );
    }
}
