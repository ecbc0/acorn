// Perfect Discrimination Tree (PDT): A pattern matching tree that ignores types during matching.
//
// Key design decisions:
// 1. Types are NOT encoded in keys - matching is purely structural
// 2. Variables are numbered by first occurrence (same as PatternTree)
// 3. When inserting a pattern, we store the types of each pattern variable
// 4. When matching, we find structural matches first, then verify type compatibility
//
// This approach naturally handles polymorphic patterns because:
// - Pattern: add[R](x, y) encodes as just the structure (ignoring that R is a type variable)
// - Query: add[Int](c, d) encodes as the same structure
// - After finding the match, we verify that the type bindings are compatible

use qp_trie::{Entry, SubTrie, Trie};

use super::atom::{Atom as KernelAtom, AtomId};
use super::clause::Clause;
use super::kernel_context::KernelContext;
use super::literal::Literal;
use super::local_context::LocalContext;
use super::symbol::Symbol;
use super::term::Term;
use super::term::{Decomposition, TermRef};
use super::unifier::{Scope, Unifier};

/// Atoms are the leaf nodes in the PDT.
/// Types are NOT represented - only symbols and variables.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Atom {
    /// Pattern variable, numbered by first occurrence.
    Variable(AtomId),

    /// Named constants and functions.
    Symbol(Symbol),

    /// Boolean constant true.
    True,

    /// Boolean constant false.
    False,
}

/// Edges form the structure of paths through the PDT.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Edge {
    /// Application: followed by function, argument.
    /// Note: unlike PatternTree, we don't encode domain type.
    Application,

    /// A leaf atom.
    Atom(Atom),

    /// Indicates a literal with the given sign (true = positive).
    LiteralForm(bool),
}

// Byte constants for serialization
const APPLICATION: u8 = 0;
const LITERAL_POSITIVE: u8 = 1;
const LITERAL_NEGATIVE: u8 = 2;
const ATOM_VARIABLE: u8 = 3;
const ATOM_TRUE: u8 = 4;
const ATOM_FALSE: u8 = 5;
const ATOM_SYMBOL_GLOBAL: u8 = 6;
const ATOM_SYMBOL_SCOPED: u8 = 7;
const ATOM_SYMBOL_SYNTHETIC: u8 = 8;
const ATOM_SYMBOL_EMPTY: u8 = 9;
const ATOM_SYMBOL_BOOL: u8 = 10;
const ATOM_SYMBOL_TYPESORT: u8 = 11;
const ATOM_SYMBOL_TYPE: u8 = 12;

impl Edge {
    /// Returns the discriminant byte for this edge.
    fn discriminant(&self) -> u8 {
        match self {
            Edge::Application => APPLICATION,
            Edge::LiteralForm(true) => LITERAL_POSITIVE,
            Edge::LiteralForm(false) => LITERAL_NEGATIVE,
            Edge::Atom(atom) => match atom {
                Atom::Variable(_) => ATOM_VARIABLE,
                Atom::True => ATOM_TRUE,
                Atom::False => ATOM_FALSE,
                Atom::Symbol(Symbol::True) => ATOM_TRUE,
                Atom::Symbol(Symbol::False) => ATOM_FALSE,
                Atom::Symbol(Symbol::Empty) => ATOM_SYMBOL_EMPTY,
                Atom::Symbol(Symbol::Bool) => ATOM_SYMBOL_BOOL,
                Atom::Symbol(Symbol::TypeSort) => ATOM_SYMBOL_TYPESORT,
                Atom::Symbol(Symbol::Type(_)) => ATOM_SYMBOL_TYPE,
                Atom::Symbol(Symbol::GlobalConstant(_)) => ATOM_SYMBOL_GLOBAL,
                Atom::Symbol(Symbol::ScopedConstant(_)) => ATOM_SYMBOL_SCOPED,
                Atom::Symbol(Symbol::Synthetic(_)) => ATOM_SYMBOL_SYNTHETIC,
            },
        }
    }

    /// Appends the byte representation of this edge to the vector.
    /// Each edge is 3 bytes: discriminant + 2 bytes for ID (if applicable).
    fn append_to(&self, v: &mut Vec<u8>) {
        v.push(self.discriminant());
        let id: u16 = match self {
            Edge::Application | Edge::LiteralForm(_) => 0,
            Edge::Atom(atom) => match atom {
                Atom::Variable(i) => *i,
                Atom::True | Atom::False => 0,
                Atom::Symbol(Symbol::True) | Atom::Symbol(Symbol::False) => 0,
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
    fn from_bytes(byte1: u8, byte2: u8, byte3: u8) -> Edge {
        use super::types::GroundTypeId;
        let id = u16::from_ne_bytes([byte2, byte3]);
        match byte1 {
            APPLICATION => Edge::Application,
            LITERAL_POSITIVE => Edge::LiteralForm(true),
            LITERAL_NEGATIVE => Edge::LiteralForm(false),
            ATOM_VARIABLE => Edge::Atom(Atom::Variable(id)),
            ATOM_TRUE => Edge::Atom(Atom::True),
            ATOM_FALSE => Edge::Atom(Atom::False),
            ATOM_SYMBOL_GLOBAL => Edge::Atom(Atom::Symbol(Symbol::GlobalConstant(id))),
            ATOM_SYMBOL_SCOPED => Edge::Atom(Atom::Symbol(Symbol::ScopedConstant(id))),
            ATOM_SYMBOL_SYNTHETIC => Edge::Atom(Atom::Symbol(Symbol::Synthetic(id))),
            ATOM_SYMBOL_EMPTY => Edge::Atom(Atom::Symbol(Symbol::Empty)),
            ATOM_SYMBOL_BOOL => Edge::Atom(Atom::Symbol(Symbol::Bool)),
            ATOM_SYMBOL_TYPESORT => Edge::Atom(Atom::Symbol(Symbol::TypeSort)),
            ATOM_SYMBOL_TYPE => Edge::Atom(Atom::Symbol(Symbol::Type(GroundTypeId::new(id)))),
            _ => panic!("invalid PDT edge discriminant: {}", byte1),
        }
    }

    /// Debug helper to convert a byte sequence to a string of edges.
    #[allow(dead_code)]
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

/// Encodes the structure of a term (ignoring types).
fn key_from_term_structure(term: TermRef, key: &mut Vec<u8>) {
    match term.decompose() {
        Decomposition::Atom(atom) => {
            let edge_atom = match atom {
                KernelAtom::FreeVariable(v) => Atom::Variable(*v),
                KernelAtom::BoundVariable(i) => {
                    panic!(
                        "BoundVariable({}) in PDT term - should have been substituted",
                        i
                    )
                }
                KernelAtom::Symbol(Symbol::True) => Atom::True,
                KernelAtom::Symbol(Symbol::False) => Atom::False,
                KernelAtom::Symbol(s) => Atom::Symbol(*s),
                KernelAtom::Typeclass(_) => {
                    // Typeclasses are handled as part of type-checking, not structure
                    panic!("Typeclass in PDT term structure - should be in type context")
                }
            };
            Edge::Atom(edge_atom).append_to(key);
        }
        Decomposition::Application(func, arg) => {
            // Application: just encode func and arg, no type info
            Edge::Application.append_to(key);
            key_from_term_structure(func, key);
            key_from_term_structure(arg, key);
        }
        Decomposition::Pi(_, _) => {
            panic!("Pi types should not appear in PDT term structure encoding");
        }
    }
}

/// Generates a complete key for a term (ignoring types).
fn key_from_term(term: &Term) -> Vec<u8> {
    let mut key = Vec::new();
    key_from_term_structure(term.as_ref(), &mut key);
    key
}

/// Generates a key for a term pair (like a literal without sign).
fn key_from_pair(term1: &Term, term2: &Term) -> Vec<u8> {
    let mut key = Vec::new();
    key_from_term_structure(term1.as_ref(), &mut key);
    key_from_term_structure(term2.as_ref(), &mut key);
    key
}

/// Generates a key for a clause.
fn key_from_clause(clause: &Clause) -> Vec<u8> {
    let mut key = Vec::new();
    for literal in &clause.literals {
        Edge::LiteralForm(literal.positive).append_to(&mut key);
    }
    for literal in &clause.literals {
        key_from_term_structure(literal.left.as_ref(), &mut key);
        key_from_term_structure(literal.right.as_ref(), &mut key);
    }
    key
}

/// Creates a key prefix for a term (currently empty).
pub fn term_key_prefix() -> Vec<u8> {
    Vec::new()
}

/// Stored metadata for a pattern: the types of each variable in the pattern.
#[derive(Clone, Debug)]
struct PatternMetadata {
    /// The pattern's local context, containing variable types.
    context: LocalContext,
}

impl PatternMetadata {
    fn from_clause(clause: &Clause) -> PatternMetadata {
        PatternMetadata {
            context: clause.get_local_context().clone(),
        }
    }

    fn from_local_context(lctx: &LocalContext) -> PatternMetadata {
        PatternMetadata {
            context: lctx.clone(),
        }
    }
}

/// Perfect Discrimination Tree: pattern matching that ignores types during structural matching.
#[derive(Clone, Debug)]
pub struct Pdt<T> {
    /// Maps byte keys to indices into the values vector.
    trie: Trie<Vec<u8>, usize>,

    /// Values stored in the tree.
    pub values: Vec<T>,

    /// Metadata for each pattern (variable types for type-checking).
    metadata: Vec<PatternMetadata>,
}

impl<T> Pdt<T> {
    pub fn new() -> Pdt<T> {
        Pdt {
            trie: Trie::new(),
            values: vec![],
            metadata: vec![],
        }
    }

    /// Inserts a term pair with its associated value.
    fn insert_pair(&mut self, term1: &Term, term2: &Term, value: T, local_context: &LocalContext) {
        let key = key_from_pair(term1, term2);
        let value_id = self.values.len();
        self.values.push(value);
        self.metadata
            .push(PatternMetadata::from_local_context(local_context));
        self.trie.insert(key, value_id);
    }

    /// Inserts a clause with its associated value.
    pub fn insert_clause(&mut self, clause: &Clause, value: T, _kernel_context: &KernelContext) {
        let key = key_from_clause(clause);
        let value_id = self.values.len();
        self.values.push(value);
        self.metadata.push(PatternMetadata::from_clause(clause));
        self.trie.insert(key, value_id);
    }

    /// Finds matches for a term, calling the callback for each match.
    /// Returns false if callback returns false, otherwise true.
    ///
    /// The key parameter is used as a prefix (e.g., type info for API compatibility).
    /// The type checking happens via the metadata after structural matching.
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
        // Get subtrie based on any prefix in key
        let subtrie = self.trie.subtrie(key);
        find_matches_while(
            &subtrie,
            key,
            terms,
            local_context,
            kernel_context,
            &self.metadata,
            500,
            replacements,
            callback,
        )
    }

    /// Finds a pair in the tree.
    fn find_pair<'a>(
        &'a self,
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<&'a T> {
        let terms = [left.as_ref(), right.as_ref()];
        let mut replacements: Vec<TermRef> = vec![];
        let mut found_id = None;
        let mut key = Vec::new();
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

        // Build the terms array from all literals in the clause
        let mut terms: Vec<TermRef> = vec![];
        for literal in &clause.literals {
            terms.push(literal.left.as_ref());
            terms.push(literal.right.as_ref());
        }

        // Build prefix key (just literal signs)
        let mut prefix_key = Vec::new();
        for literal in &clause.literals {
            Edge::LiteralForm(literal.positive).append_to(&mut prefix_key);
        }

        let subtrie = self.trie.subtrie(&prefix_key);

        let mut replacements: Vec<TermRef> = vec![];
        let mut found_id = None;
        find_matches_while(
            &subtrie,
            &mut prefix_key,
            &terms,
            local_context,
            kernel_context,
            &self.metadata,
            500,
            &mut replacements,
            &mut |value_id, _| {
                found_id = Some(value_id);
                false // Stop after first match
            },
        );
        found_id.map(|id| &self.values[id])
    }
}

impl Pdt<()> {
    /// Appends to the existing value if possible. Otherwise, inserts a vec![U].
    pub fn insert_or_append<U>(
        pt: &mut Pdt<Vec<U>>,
        term: &Term,
        value: U,
        local_context: &LocalContext,
        _kernel_context: &KernelContext,
    ) {
        let key = key_from_term(term);
        match pt.trie.entry(key) {
            Entry::Occupied(entry) => {
                let value_id = entry.get();
                pt.values[*value_id].push(value);
            }
            Entry::Vacant(entry) => {
                let value_id = pt.values.len();
                pt.values.push(vec![value]);
                pt.metadata
                    .push(PatternMetadata::from_local_context(local_context));
                entry.insert(value_id);
            }
        }
    }
}

/// The LiteralSet stores literals using a PDT.
#[derive(Clone)]
pub struct LiteralSet {
    /// Stores (sign, id, flipped) for each literal.
    tree: Pdt<(bool, usize, bool)>,
}

impl LiteralSet {
    pub fn new() -> LiteralSet {
        LiteralSet { tree: Pdt::new() }
    }

    /// Inserts a literal along with its id.
    pub fn insert(
        &mut self,
        literal: &Literal,
        id: usize,
        local_context: &LocalContext,
        _kernel_context: &KernelContext,
    ) {
        self.tree.insert_pair(
            &literal.left,
            &literal.right,
            (literal.positive, id, false),
            local_context,
        );
        if !literal.strict_kbo() {
            let (right, left, reversed_context) = literal.normalized_reversed(local_context);
            self.tree.insert_pair(
                &right,
                &left,
                (literal.positive, id, true),
                &reversed_context,
            );
        }
    }

    /// Checks whether any literal in the tree is a generalization of the provided literal.
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

/// Checks if a binding is type-compatible with the pattern variable's type.
///
/// For polymorphic patterns, this checks that the bound term's type can be obtained
/// by instantiating the pattern variable's type. Uses the Unifier to check if the
/// bound type is a valid instance of the pattern type (e.g., List[Int] matches List[T]).
fn types_compatible(
    bound_term: TermRef,
    pattern_var_type: &Term,
    pattern_context: &LocalContext,
    query_context: &LocalContext,
    kernel_context: &KernelContext,
) -> bool {
    let bound_type = bound_term.get_type_with_context(query_context, kernel_context);

    // Fast path: exact equality
    if bound_type == *pattern_var_type {
        return true;
    }

    // Special case: pattern variable type is a typeclass constraint
    // E.g., x0: Ring means x0 is a type that implements Ring
    // If bound_term is a concrete type (like Int), check if it implements the typeclass
    if let Decomposition::Atom(KernelAtom::Typeclass(tc_id)) = pattern_var_type.as_ref().decompose()
    {
        // The bound term should be a type that implements this typeclass
        if let Some(ground_id) = bound_term.as_type_atom() {
            return kernel_context.type_store.is_instance_of(ground_id, *tc_id);
        }
        // If it's a type variable, accept it (polymorphic matching)
        if let Decomposition::Atom(KernelAtom::FreeVariable(_)) = bound_term.decompose() {
            return true;
        }
        return false;
    }

    // Special case: pattern variable type is a type variable (FreeVariable)
    // E.g., x1: x0 where x0 is a type variable. We need to check if bound_type
    // is compatible with x0's constraints.
    if let Decomposition::Atom(KernelAtom::FreeVariable(var_id)) =
        pattern_var_type.as_ref().decompose()
    {
        // Look up what x0's type is (should be a typeclass like Ring, or Type)
        if let Some(var_type) = pattern_context.get_var_type(*var_id as usize) {
            if let Decomposition::Atom(KernelAtom::Typeclass(tc_id)) = var_type.as_ref().decompose()
            {
                // bound_type should implement this typeclass
                if let Some(ground_id) = bound_type.as_ref().as_type_atom() {
                    return kernel_context.type_store.is_instance_of(ground_id, *tc_id);
                }
            }
            // If x0's type is Type/TypeSort (not a typeclass constraint), accept any type
            if matches!(
                var_type.as_ref().decompose(),
                Decomposition::Atom(KernelAtom::Symbol(Symbol::TypeSort))
            ) {
                return true;
            }
        }
        // Otherwise, try regular unification
    }

    // Use Unifier to check if bound_type is an instance of pattern_var_type
    // This handles cases like List[Int] matching List[T] where T is a type variable
    let mut unifier = Unifier::new(3, kernel_context);
    unifier.set_input_context(Scope::LEFT, pattern_context);
    unifier.set_input_context(Scope::RIGHT, query_context);

    // Try to unify pattern_var_type (LEFT) with bound_type (RIGHT)
    unifier.unify(Scope::LEFT, pattern_var_type, Scope::RIGHT, &bound_type)
}

/// Matches a sequence of terms against patterns in the trie.
///
/// Unlike PatternTree, this matches purely on structure (ignoring types).
/// After finding a structural match, it verifies type compatibility.
///
/// The key insight is that we navigate the trie by trying different edges:
/// - Variable(n) edges represent pattern variables that can match any query term
/// - Structural edges (Application, Symbol atoms) must match the query term exactly
fn find_matches_while<'a, F>(
    subtrie: &SubTrie<Vec<u8>, usize>,
    key: &mut Vec<u8>,
    terms: &[TermRef<'a>],
    local_context: &LocalContext,
    kernel_context: &KernelContext,
    all_metadata: &[PatternMetadata],
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
        eprintln!("WARNING: PDT stack_limit exhausted - consider increasing the limit");
        return false;
    }

    if terms.is_empty() {
        match subtrie.get(key as &[u8]) {
            Some(value_id) => {
                // Structural match found - verify type compatibility
                let metadata = &all_metadata[*value_id];
                if verify_type_compatibility(replacements, metadata, local_context, kernel_context)
                {
                    return callback(*value_id, replacements);
                }
                return true; // Type mismatch, continue searching
            }
            None => {
                let (sample, _) = subtrie.iter().next().unwrap();
                panic!(
                    "\nPDT key mismatch.\nquerying: {}\nexisting: {}\n",
                    Edge::debug_bytes(key),
                    Edge::debug_bytes(sample)
                );
            }
        }
    }

    let initial_key_len = key.len();
    let first = terms[0];
    let rest = &terms[1..];

    // Case 1: the first query term could match an existing replacement (backreference)
    // This means the pattern has Variable(i) where i is an already-bound variable
    for i in 0..replacements.len() {
        if first == replacements[i] {
            Edge::Atom(Atom::Variable(i as u16)).append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);
            if !new_subtrie.is_empty() {
                if !find_matches_while(
                    &new_subtrie,
                    key,
                    rest,
                    local_context,
                    kernel_context,
                    all_metadata,
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

    // Case 2: the first query term could match a new pattern variable
    // This means the pattern has Variable(n) where n is the next new variable
    {
        Edge::Atom(Atom::Variable(replacements.len() as u16)).append_to(key);
        let new_subtrie = subtrie.subtrie(key as &[u8]);
        if !new_subtrie.is_empty() {
            replacements.push(first);
            if !find_matches_while(
                &new_subtrie,
                key,
                rest,
                local_context,
                kernel_context,
                all_metadata,
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

    // Case 3: structural match - the pattern has the same structure as the query
    // FreeVariables in the query should only match via Cases 1/2 (pattern variables),
    // not via structural matching. All Variables in patterns are wildcards.
    match first.decompose() {
        Decomposition::Atom(atom) => {
            let edge_atom = match atom {
                KernelAtom::FreeVariable(_) => {
                    // Query has a variable - it can only match pattern variables via Cases 1/2
                    // Skip structural matching for FreeVariables
                    None
                }
                KernelAtom::BoundVariable(i) => {
                    panic!(
                        "BoundVariable({}) in PDT search - should have been substituted",
                        i
                    )
                }
                KernelAtom::Symbol(Symbol::True) => Some(Atom::True),
                KernelAtom::Symbol(Symbol::False) => Some(Atom::False),
                KernelAtom::Symbol(s) => Some(Atom::Symbol(*s)),
                KernelAtom::Typeclass(_) => return true, // Skip typeclasses in structure
            };
            if let Some(edge_atom) = edge_atom {
                Edge::Atom(edge_atom).append_to(key);
                let new_subtrie = subtrie.subtrie(key as &[u8]);
                if !new_subtrie.is_empty() {
                    if !find_matches_while(
                        &new_subtrie,
                        key,
                        rest,
                        local_context,
                        kernel_context,
                        all_metadata,
                        stack_limit - 1,
                        replacements,
                        callback,
                    ) {
                        return false;
                    }
                }
            }
        }
        Decomposition::Application(func, arg) => {
            Edge::Application.append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);

            if !new_subtrie.is_empty() {
                // Build new terms: [func, arg, ...rest]
                let mut new_terms: Vec<TermRef<'a>> = Vec::with_capacity(2 + rest.len());
                new_terms.push(func);
                new_terms.push(arg);
                new_terms.extend_from_slice(rest);

                if !find_matches_while(
                    &new_subtrie,
                    key,
                    &new_terms,
                    local_context,
                    kernel_context,
                    all_metadata,
                    stack_limit - 1,
                    replacements,
                    callback,
                ) {
                    return false;
                }
            }
        }
        Decomposition::Pi(_, _) => {
            panic!("Pi types should not appear in PDT matching");
        }
    }

    key.truncate(initial_key_len);
    true
}

/// Verify that the replacements have types compatible with the pattern variables.
fn verify_type_compatibility(
    replacements: &[TermRef],
    metadata: &PatternMetadata,
    query_context: &LocalContext,
    kernel_context: &KernelContext,
) -> bool {
    let pattern_var_types = metadata.context.get_var_types();
    for (i, &replacement) in replacements.iter().enumerate() {
        if i >= pattern_var_types.len() {
            // Pattern didn't have this many variables - that's fine
            continue;
        }
        let pattern_var_type = &pattern_var_types[i];
        if !types_compatible(
            replacement,
            pattern_var_type,
            &metadata.context,
            query_context,
            kernel_context,
        ) {
            return false;
        }
    }
    true
}

/// Replaces variables in a term with corresponding replacement terms.
/// (Re-exported from pattern_tree for API compatibility)
pub use super::pattern_tree::replace_term_variables;

/// Type alias to allow using Pdt with the same name as PatternTree.
/// This enables feature-flag-based switching.
pub type PatternTree<T> = Pdt<T>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_edge_roundtrip() {
        let edges = vec![
            Edge::Application,
            Edge::LiteralForm(true),
            Edge::LiteralForm(false),
            Edge::Atom(Atom::Variable(0)),
            Edge::Atom(Atom::Variable(42)),
            Edge::Atom(Atom::True),
            Edge::Atom(Atom::False),
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
    fn test_pdt_insert_and_find_clause() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2", "c3", "c4"], "Bool");

        let mut tree: Pdt<usize> = Pdt::new();

        // Insert pattern: x0 = x0
        let clause = kctx.parse_clause("x0 = x0", &["Bool"]);
        tree.insert_clause(&clause, 42, &kctx);

        // Query: c5 = c5 should match
        kctx.parse_constant("c5", "Bool");
        let special = kctx.parse_clause("c5 = c5", &[]);
        let found = tree.find_clause(&special, &kctx);
        assert_eq!(found, Some(&42));
    }

    #[test]
    fn test_pdt_variable_matching() {
        // Test that patterns with variables match concrete terms
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2", "c3", "c4"], "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree: Pdt<usize> = Pdt::new();

        // Insert pattern "x0 = c0" - a variable equals a constant
        let pattern_left = Term::parse("x0");
        let pattern_right = Term::parse("c0");
        tree.insert_pair(&pattern_left, &pattern_right, 7, &lctx);

        // Query "c1 = c0" should match (c1 can be matched by variable x0)
        let query_lctx = kctx.parse_local(&[]);
        let query_left = Term::parse("c1");
        let query_right = Term::parse("c0");
        let found = tree.find_pair(&query_left, &query_right, &query_lctx, &kctx);
        assert_eq!(found, Some(&7));
    }

    #[test]
    fn test_pdt_application() {
        // Test that patterns with function applications and variables match correctly
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c5", "c6"], "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree: Pdt<usize> = Pdt::new();

        // Insert pattern "c1(x0) = c5" - a function applied to a variable equals a constant
        let pattern_left = Term::parse("c1(x0)");
        let pattern_right = Term::parse("c5");
        tree.insert_pair(&pattern_left, &pattern_right, 42, &lctx);

        // Query "c1(c6) = c5" should match (c6 : Bool can be matched by variable x0)
        let query_lctx = kctx.parse_local(&[]);
        let query_left = Term::parse("c1(c6)");
        let query_right = Term::parse("c5");
        let found = tree.find_pair(&query_left, &query_right, &query_lctx, &kctx);
        assert_eq!(found, Some(&42));
    }

    #[test]
    fn test_pdt_polymorphic_clause_matching() {
        // Test: Pattern is `add[R](x, y) = add[R](y, x)` for any R: Ring
        // Query is `add[Int](c, f(d)) = add[Int](f(d), c)` where Int: Ring
        // The query should match the pattern.

        let mut kctx = KernelContext::new();

        // Register Ring typeclass and mark Int as implementing Ring
        kctx.parse_typeclass("Ring").parse_instance("Int", "Ring");

        // Create `add` with polymorphic type: Π(R: Ring). R -> R -> R
        kctx.parse_polymorphic_constant("c0", "R: Ring", "R -> R -> R"); // add

        // Create constants for the query
        kctx.parse_constant("c1", "Int -> Int"); // f
        kctx.parse_constants(&["c2", "c3"], "Int"); // c, d

        // Pattern clause: add[R](x, y) = add[R](y, x)
        // x0: Ring (type variable R), x1: x0 (value x), x2: x0 (value y)
        let pattern_clause =
            kctx.parse_clause("c0(x0, x1, x2) = c0(x0, x2, x1)", &["Ring", "x0", "x0"]);

        // Insert pattern into tree
        let mut tree: Pdt<&str> = Pdt::new();
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

    #[test]
    fn test_pdt_parameterized_type_matching() {
        // Tests that types_compatible() handles type instantiation correctly.
        //
        // Pattern: reverse(x) = x where x : List[T] (T is a type variable)
        // Query: reverse(mylist) = mylist where mylist : List[Int]
        //
        // The pattern variable x has type List[T] (a parameterized type with type variable).
        // The query term mylist has type List[Int] (a concrete instantiation).
        //
        // For this to match, we need to recognize that List[Int] is an instance of List[T]
        // by binding T -> Int. The current simple equality check fails because:
        // - List[T] != List[Int]
        // - List[T] is not a FreeVariable atom (it's an Application)

        let mut kctx = KernelContext::new();

        // Set up types
        kctx.parse_datatype("Int");
        kctx.parse_type_constructor("List", 1);

        // reverse : forall T. List[T] -> List[T]
        kctx.parse_polymorphic_constant("c0", "T: Type", "List[T] -> List[T]"); // reverse

        // mylist : List[Int]
        kctx.parse_constant("c1", "List[Int]"); // mylist

        let mut tree: Pdt<&str> = Pdt::new();

        // Pattern clause: reverse[T](x) = x where T: Type, x : List[T]
        // x0 is a type variable T (type: Type)
        // x1 has type List[x0] = List[T]
        let pattern_clause = kctx.parse_clause("c0(x0, x1) = x1", &["Type", "List[x0]"]);
        tree.insert_clause(&pattern_clause, "reverse_identity", &kctx);

        // Query clause: reverse[Int](mylist) = mylist where mylist : List[Int]
        let query_clause = kctx.parse_clause("c0(Int, c1) = c1", &[]);

        let found = tree.find_clause(&query_clause, &kctx);

        // This should match with T -> Int, x -> mylist
        // Currently fails because List[T] != List[Int] and we don't do type instantiation
        assert_eq!(
            found,
            Some(&"reverse_identity"),
            "Query with List[Int] should match pattern with List[T]"
        );
    }

    #[test]
    fn test_pdt_query_variable_matches_pattern_variable() {
        // Tests that a FreeVariable in the query can match a pattern variable,
        // even when the variable IDs differ.
        //
        // This test uses find_term_matches_while directly to avoid clause normalization.
        //
        // Pattern: c0(x0) where x0 is variable 0
        // Query: c0(x1) where x1 is variable 1 (different ID)
        //
        // The pattern variable x0 should match the query's FreeVariable x1.

        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool -> Bool");

        // Pattern: c0(x0) with x0 : Bool (variable ID 0)
        let pattern_lctx = kctx.parse_local(&["Bool"]);
        let pattern_term = Term::parse("c0(x0)");

        let mut tree: Pdt<&str> = Pdt::new();
        tree.insert_pair(&pattern_term, &Term::new_true(), "pattern", &pattern_lctx);

        // Query: c0(x1) with x1 as variable ID 1 (different from pattern's x0)
        // We create a context where x0 is unused and x1 is Bool
        let query_lctx = kctx.parse_local(&["Bool", "Bool"]);
        // Build c0(x1) manually: apply c0 to FreeVariable(1)
        let x1 = Term::atom(KernelAtom::FreeVariable(1));
        let query_term = Term::parse("c0").apply(&[x1]);

        let mut key = Vec::new();
        let mut replacements = vec![];
        let mut found = false;

        tree.find_term_matches_while(
            &mut key,
            &[query_term.as_ref(), Term::new_true().as_ref()],
            &query_lctx,
            &kctx,
            &mut replacements,
            &mut |_value_id, _replacements| {
                found = true;
                true
            },
        );

        assert!(
            found,
            "Pattern c0(x0) should match query c0(x1) even with different variable IDs"
        );
    }
}
