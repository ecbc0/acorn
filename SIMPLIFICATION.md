# Simplification Proposals for Prover/Checker/Normalizer

This document outlines proposals to simplify the central proof machinery. These are **proposals, not definite plans** - they represent potential improvements identified through analysis.

## Current Architecture Overview

### The Proof Flow

```
Prover (saturation)
    -> ProofStep (symbolic, with generic variables)
    -> Proof struct (ordered list of steps)
    -> make_cert() [BACKWARD RECONSTRUCTION]
        -> reconstruct_step() for each step
        -> CodeGenerator::concrete_step_to_code()
    -> Certificate (goal name + code strings)
    -> check_cert() [VERIFICATION]
        -> Parse each code line as statement
        -> Normalize to clauses
        -> check_clause() via EqualityGraph + GeneralizationSet
    -> CertificateStep (verified)
```

### Pain Points Identified

1. **Backward reconstruction is complex** - `reconstruct_step()` in `proof.rs` is 600+ lines with custom logic for each rule type
2. **Two parsing systems** - Certificates are strings that get re-parsed, duplicating the regular code parsing
3. **Checker has hidden inference** - Automatically derives 6+ inference rules, creating non-deterministic behavior
4. **No clean intermediate representation** - Nothing between symbolic Proof and string Certificate
5. **Synthetic handling is complex** - Eager creation, key matching for deduplication, complex reconstruction
6. **Step transparency issues** - Single conceptual steps become multiple clauses during normalization

### Ideal Architecture (per user)

```
Prover -> Proof -> ConcreteProof -> Checker
                   ConcreteProof <-> Certificate (bidirectional)
```

---

## Proposal 1: Forward-Tracking Proof Construction

**Difficulty:** Medium | **Risk:** Low | **Impact:** ~600 lines removed

### The Problem

Currently, `make_cert()` in `src/prover/proof.rs` (lines 143-220) works BACKWARD from the final step. It calls `reconstruct_step()` recursively (lines 233-854) to figure out variable mappings. This backward reconstruction is complex because each rule type (Resolution, Rewrite, EqualityFactoring, etc.) needs custom logic to compute input VariableMaps from output VariableMaps.

The `reconstruct_step()` function handles:
- **Assumptions** (lines 265-307): Uses traces to match original literals with output clause
- **Rewrites** (lines 308-389): Pattern matching to figure out concrete bindings
- **Resolution** (lines 606-822): Handles long_clause, short_clause, post-resolution literals
- Plus: EqualityResolution, EqualityFactoring, Injectivity, BooleanReduction, Extensionality, Specialization

### The Solution

Track concrete variable mappings FORWARD during proof construction. When creating a `ProofStep`, immediately compute and store the `VariableMap` for that step.

### Files to Modify

**`src/proof_step.rs`:**
```rust
pub struct ProofStep {
    pub clause: Clause,
    pub truthiness: Truthiness,
    pub rule: Rule,
    pub simplification_rules: Vec<usize>,
    pub proof_size: u32,
    pub depth: u32,
    pub trace: Option<ClauseTrace>,
    pub var_map: Option<VariableMap>,  // NEW: concrete bindings
}
```

**`src/prover/active_set.rs`:**
- In `try_resolution()`, `find_rewrites()`, etc., populate `var_map` during step creation
- The unifier already computes these bindings - just capture them

**`src/prover/proof.rs`:**
- Simplify `make_cert()` to iterate forward through steps
- Remove `reconstruct_step()` entirely (or reduce to simple validation)

### Benefits

- Eliminates ~600 lines of complex backward reconstruction logic
- Makes proof structure more intuitive (data flows forward)
- Easier debugging (can inspect maps at each step)
- Foundation for proposals 2-4

### Considerations

- Memory overhead: storing VariableMap per step (~16 bytes per variable)
- Need to thread LocalContext through step creation consistently
- Must ensure all step creation paths populate the map

---

## Proposal 2: Unify Certificate Parsing with Regular Code

**Difficulty:** Medium | **Risk:** Low | **Impact:** ~150 lines removed, cleaner architecture

### The Problem

Certificates are stored as `Vec<String>` in `src/certificate.rs`. The Checker in `src/checker.rs` re-parses these strings using `Statement::parse_str_with_options()` (line 383) and evaluates through `Evaluator`. This:

1. Duplicates parsing logic (once in elaborator, once in checker)
2. Requires the Checker to maintain bindings/normalizer state
3. Makes certificate format fragile (string-based)

### The Solution

Introduce a `CertificateStatement` enum that represents parsed certificate steps:

```rust
pub enum CertificateStatement {
    /// let (type_params...) (decls...) satisfy condition
    Satisfy {
        type_params: Vec<TypeParam>,
        decls: Vec<(String, AcornType)>,
        condition: AcornValue,
    },
    /// A claim to be proven
    Claim(AcornValue),
}
```

Generate certificates as `Vec<CertificateStatement>` directly from `make_cert()`. Serialize to strings only for storage.

### Files to Modify

**`src/certificate.rs`:**
```rust
pub struct Certificate {
    pub goal: String,
    pub proof: Option<Vec<CertificateStatement>>,
}

impl Certificate {
    pub fn to_strings(&self) -> Vec<String> { ... }
    pub fn from_strings(goal: String, lines: Vec<String>) -> Result<Self, Error> { ... }
}
```

**`src/prover/proof.rs`:**
- Generate `CertificateStatement` instead of strings in `make_cert()`

**`src/checker.rs`:**
- Accept `CertificateStatement` directly in `check_cert()`
- Remove string parsing logic

**`src/code_generator.rs`:**
- Add `statement_to_string()` for serialization
- Keep existing logic for backward compatibility

### Benefits

- Type-safe certificate representation
- Eliminates redundant parsing in Checker
- Bidirectional: can convert to/from strings for storage
- Enables future optimizations (skip string intermediate)

### Considerations

- Need to bump manifest version for new certificate format
- Migration path for existing certificates (can support both formats)
- Slightly larger serialized certificates if using structured format

---

## Proposal 3: Introduce ConcreteProof Intermediate Representation

**Difficulty:** High | **Risk:** Low | **Impact:** Cleaner architecture, better debugging

### The Problem

There's no clean intermediate representation between the symbolic proof and the string certificate. The current data flow has these representations:

1. `ProofStep` - symbolic, with generic variables
2. `Proof` - collection of ProofSteps
3. `ConcreteStep` / `ConcreteStepId` - used internally during reconstruction, but not a first-class type
4. `Certificate` - just strings

### The Solution

Introduce a `ConcreteProof` struct that captures the fully-instantiated proof:

```rust
pub struct ConcreteProof {
    pub goal: String,
    pub steps: Vec<ConcreteProofStep>,
}

pub struct ConcreteProofStep {
    /// The concrete clause (no unbound variables)
    pub clause: Clause,
    /// How this step was derived
    pub rule: ConcreteRule,
    /// Indices of premise steps (for non-assumptions)
    pub dependencies: Vec<usize>,
}

pub enum ConcreteRule {
    Assumption { source: Source },
    Resolution { long: usize, short: usize },
    Rewrite { pattern: usize, target: usize, path: Vec<PathStep> },
    EqualityResolution { from: usize },
    // etc.
}
```

### New Data Flow

```
Proof
    -> to_concrete()
    -> ConcreteProof
        -> to_certificate() -> Certificate (for storage)
        -> check() -> verified (for validation)
```

And bidirectionally:
```
Certificate -> to_concrete() -> ConcreteProof
```

### Files to Modify

**New file: `src/concrete_proof.rs` (~400 lines)**
- Define `ConcreteProof`, `ConcreteProofStep`, `ConcreteRule`
- Implement validation logic
- Implement `to_certificate()` and `from_certificate()`

**`src/prover/proof.rs`:**
- Add `to_concrete(&self) -> ConcreteProof` method

**`src/checker.rs`:**
- Add `check_concrete(&self, proof: &ConcreteProof) -> Result<(), Error>`

### Benefits

- Clean separation of concerns
- Easier debugging (can inspect ConcreteProof at any stage)
- Natural place for validation
- Enables optimizations (skip string serialization in memory)
- Matches user's ideal architecture

### Considerations

- Additional abstraction layer (but well-defined)
- Memory overhead for ConcreteProof
- Need to maintain consistency between representations

---

## Proposal 4: Reduce Automatic Inference in Checker

**Difficulty:** High | **Risk:** Medium | **Impact:** Deterministic checker, easier debugging

### The Problem

The Checker in `src/checker.rs` automatically derives 6 inference rules when inserting clauses (`insert_clause()` lines 161-239):

1. **Equality resolution** (lines 187-193) - from `a = a` derive contradiction
2. **Extensionality** (lines 195-202) - from `f != g` derive `f(x) != g(x)`
3. **Equality factoring** (lines 209-217) - factor equal terms
4. **Injectivity** (lines 219-224) - from `C(a) = C(b)` derive `a = b`
5. **Boolean reduction** (lines 226-239) - simplify boolean expressions

This creates:
- Non-deterministic behavior (order matters)
- Potential exponential blowup
- Hard to debug (hidden inference chains)
- Cycle detection needed (`past_boolean_reductions`)

### The Solution

Make inference rule derivation EXPLICIT in certificates:

```rust
pub enum CertificateStep {
    /// A direct claim
    Claim(AcornValue),
    /// Apply equality resolution to step N
    EqualityResolution { from: usize },
    /// Apply extensionality to step N
    Extensionality { from: usize },
    /// Apply equality factoring to step N
    EqualityFactoring { from: usize },
    /// Apply injectivity to step N
    Injectivity { from: usize },
    /// Apply boolean reduction to step N
    BooleanReduction { from: usize },
}
```

The Checker only inserts what it's explicitly told. The code generator produces these explicit steps during `make_cert()`.

### Files to Modify

**`src/checker.rs`:**
- Remove automatic inference from `insert_clause()`
- Add explicit handlers: `apply_equality_resolution(step_idx)`, etc.
- `check_clause()` becomes simpler (just lookup, no derivation)

**`src/certificate.rs`:**
- Add new statement types for inference rules

**`src/code_generator.rs`:**
- Generate explicit inference steps when needed

### Benefits

- Checker becomes deterministic and predictable
- No hidden inference chains
- Easier to debug certificate failures
- Potentially faster (no automatic derivation)
- Clearer separation between "what the prover found" and "what the checker knows"

### Considerations

- Larger certificates (need explicit steps for each inference)
- More work in code generator to track when inference is needed
- May need to track more during proof construction
- Need to identify all places where inference is currently implicit

---

## Proposal 5: Simplify Synthetic Handling with Delayed Expansion

**Difficulty:** Very High | **Risk:** High | **Impact:** Simpler normalizer, cleaner proof structure

### The Problem

The normalizer in `src/normalizer.rs` creates synthetic atoms eagerly for:
- Exists quantifiers (skolemization)
- Boolean expressions that can't be converted to terms
- Boolean function equality

This leads to:
- Complex `SyntheticDefinition` tracking (lines 27-100)
- `SyntheticKey` matching to avoid duplicates (lines 67-100)
- Complex reconstruction in `code_generator.rs` to output synthetic definitions
- Many synthetics created that are never used

The `eq_to_cnf` function (starting at line 1107) is particularly complex:
- Boolean functional inequality (lines 1155-1204) creates skolems
- Boolean equality expansion (lines 1323-1328) creates multiple clauses
- Comment at lines 1304-1305 notes: "This logic duplicates subterms"

### The Solution

Delay synthetic atom creation until proof is complete, using placeholder terms during proving:

```rust
// In src/kernel/atom.rs
pub enum Atom {
    // ... existing variants ...
    ExistentialPlaceholder(u32),  // NEW: placeholder for delayed skolemization
}
```

### New Flow

1. During normalization, use `ExistentialPlaceholder(id)` instead of creating synthetics
2. Track which placeholders appear in each clause
3. Prover treats placeholders like variables (can unify with anything of right type)
4. After proof found, instantiate only the used placeholders as synthetics
5. In certificate, output `let ... satisfy` only for used synthetics

### Files to Modify

**`src/kernel/atom.rs`:**
- Add `ExistentialPlaceholder(u32)` variant

**`src/normalizer.rs`:**
- Replace `make_skolem_terms()` with `make_placeholder_terms()`
- Remove or simplify `SyntheticDefinition`, `SyntheticKey` logic
- Track placeholder-to-type mapping

**`src/prover/proof.rs`:**
- Track which placeholders are used in the final proof
- `make_cert()` instantiates used placeholders

**`src/code_generator.rs`:**
- Generate `let...satisfy` from placeholder info

### Benefits

- Only create synthetics that are actually used
- Simpler normalizer (no synthetic key matching, no deduplication)
- Cleaner proof structure (placeholders are more uniform)
- Potentially faster proving (fewer unused synthetics to track)

### Considerations

- Significant refactor touching core data structures (Atom)
- Need to handle placeholders throughout the prover (unification, matching)
- May affect performance if placeholder checking is expensive
- Testing complexity: need to verify all paths still work
- Should be done after other changes stabilize

---

## Background: Normalization and Step Transparency

### How Normalization Works

The normalizer converts user-level logical statements (`AcornValue`) into CNF (`Clause` objects):

1. **Lambda expansion** (line 2062): `value.expand_lambdas(0)` - eagerly expands all lambdas
2. **Goal separation**: splits implications into hypotheses and counterfactuals
3. **CNF conversion** (`value_to_cnf`): recursively decomposes values into clauses
4. **Synthetic creation**: for exists quantifiers and boolean expressions

### Step Transparency Issues

Many transformations that should be a single "conceptual step" become multiple clauses:

**Boolean Equality Expansion:**
```
a = b
  -> (a implies b) and (b implies a)
  -> (not a or b) and (not b or a)
  -> 2 clauses: [not a or b], [not b or a]
```

**Boolean Function Comparison:**
```
f = g  where f,g: Nat -> Bool
  -> forall(x: Nat) { f(x) = g(x) }
  -> 2 clauses per application point
```

**Synthetic Atoms for Boolean Expressions:**
```
s0(free_vars) = (a or b)
  -> 3+ clauses: [s0 OR a OR b], [NOT a OR s0], [NOT b OR s0]
```

This creates a "step transparency gap": the user's single conceptual step becomes multiple proof obligations.

### Key Normalization Code Locations

- Entry points: `normalize_fact` (line 2146), `normalize_goal` (line 2296)
- Core CNF: `value_to_cnf` (lines 713-835)
- Boolean equality: `eq_to_cnf` (lines 1107-1335)
- Synthetic creation: `make_skolem_terms` (lines 914-1026)
- Denormalization: `denormalize` (lines 2685-2793)

---

## Background: Checker Architecture

### Core Data Structures

**EqualityGraph** (`src/kernel/equality_graph.rs`, 2100+ lines):
- Union-find + congruence closure
- Tracks term equivalences
- Handles rewrite chains
- Detects contradictions

**GeneralizationSet / PDT** (`src/kernel/pdt.rs`, 1500+ lines):
- Perfect Discrimination Tree
- Pattern matching that ignores types during matching
- Verifies type compatibility after structural match

### Checker Validation Flow

```rust
pub fn check_clause(&mut self, clause: &Clause, ...) -> Option<StepReason> {
    // 1. Try EqualityGraph (concrete reasoning)
    if let Some(reason) = self.term_graph.check_clause(clause) {
        return Some(reason);
    }

    // 2. Try GeneralizationSet (pattern matching with variables)
    if let Some(reason) = self.generalization_set.check_clause(clause) {
        return Some(reason);
    }

    // 3. Try last-argument elimination (fallback)
    // ... polymorphic matching fallback

    None // Not provable in one step
}
```

### Complexity Hotspots

1. **Variable renumbering cascades**: `LocalContext::remap()` updates all type references
2. **Trace composition**: `ClauseTrace::compose()` chains get deeply nested
3. **EqualityGraph merges**: maintain invariants during group merges
4. **Inference rule chaining**: automatic rules can trigger more rules

---

## Recommended Approach

If pursuing these proposals, the recommended order is:

1. **Proposal 1 (Forward Tracking)** - highest simplification per effort, foundation for others
2. **Proposal 2 (Unified Parsing)** - builds on cleaner proof flow
3. **Proposal 3 (ConcreteProof IR)** - provides clean architecture
4. **Proposal 4 (Explicit Inference)** - can be done independently
5. **Proposal 5 (Delayed Synthetics)** - highest risk, do last

Each proposal can be done independently, but 1 → 2 → 3 builds naturally.
