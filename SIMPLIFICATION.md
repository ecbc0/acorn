# Plan: Simplifying Proof Reconstruction

This document outlines a plan to simplify the proof reconstruction machinery. The main pain point
is `reconstruct_step()` in `src/prover/proof.rs`, which is 500+ lines of per-rule backward
reconstruction logic. The plan attacks this in two steps.

## Step 1: Separate simplification into its own proof step

### Problem

Currently, simplification is folded into the proof step that produced the clause.
`ProofStep::simplified()` (in `src/proof_step.rs`) takes a step whose rule is something like
Resolution, replaces its clause with the simplified version, and appends the simplifying steps
to `simplification_rules: Vec<usize>`. So a single `ProofStep` represents two operations: the
inference and the simplification.

This means:
- The trace has to track both operations via `ClauseTrace::compose()`, composing the inference
  trace with the simplification trace.
- Reconstruction has to untangle two composed transformations at once.
- The `simplification_rules` field is a separate side-channel of dependencies, handled differently
  from the main rule's premises.

### Solution

Make simplification a separate `Rule` variant. When `active_set.simplify()` modifies a clause,
instead of mutating the existing step, it produces a new `ProofStep` with a `Rule::Simplification`
that references the unsimplified step as its premise. Each step then represents exactly one
operation, with one trace covering one transformation.

### What changes

- **`src/proof_step.rs`**: Add `Rule::Simplification` variant. Remove the `simplification_rules`
  field from `ProofStep`. Remove `ProofStep::simplified()`.
- **`src/prover/active_set.rs`**: `simplify()` returns a separate simplification step (or the
  original step unchanged). The unsimplified step needs a `ProofStepId` so the simplification
  step can reference it.
- **`src/prover/prover.rs`**: Handle the new two-step flow when activating clauses. Both the
  unsimplified and simplified steps need to be tracked in the proof.
- **`src/prover/proof.rs`**: `reconstruct_step` gets a new `Rule::Simplification` case, which
  should be straightforward (the trace directly describes the literal mapping). Remove the
  composed-trace handling from other rule cases.

### Benefits

- Each proof step has a single trace describing a single operation.
- `simplification_rules` field goes away.
- Reconstruction for non-simplification rules gets simpler (no composed traces to untangle).
- The simplification step itself has a clean, simple reconstruction (just literal elimination).

### Considerations

- The unsimplified clause is currently ephemeral -- never stored. It will need a `ProofStepId`
  so the simplification step can reference it. This could be a new `ProofStepId` variant (e.g.,
  `Unsimplified`) or the step could be stored in the passive set.
- More steps in the proof, but individually simpler.

## Step 2: Enrich proof steps to make reconstruction mechanical

### Problem

`reconstruct_step()` works backward: given a concrete var_map for a step's conclusion, it
re-derives the var_maps for each premise. This requires per-rule-type logic because the
structural relationship between premises and conclusion is different for each rule. But at
step creation time, the prover already computed the unification between premises -- it just
didn't save it.

The traces capture part of this (which literal went where, whether it was flipped) but not the
variable-level relationships (how variables from premise A relate to variables from premise B
and the output).

### Solution

Store additional structural information in the `ProofStep` (or its `Rule` variants) at creation
time -- enough that given a conclusion var_map, computing premise var_maps becomes a single
generic operation rather than per-rule logic.

This is not a "concrete" var_map (the step is still symbolic with variables). It's a record of
the unification bindings between premise scopes -- the recipe for how the step was derived.
Think of it as an extended trace that covers variable relationships in addition to literal
relationships.

Specifically, for each rule type that involves unification (Resolution, Rewrite,
EqualityFactoring, EqualityResolution, etc.), the step would store the output of the unifier:
the bindings that map each premise's variables into a common output space. Then reconstruction
becomes: apply the conclusion var_map to those stored bindings to get each premise's var_map.

### What changes

- **`src/proof_step.rs`**: Each `Rule` variant (or a shared field) gains a field capturing the
  unifier output -- the cross-premise variable bindings.
- **`src/prover/active_set.rs`**: At step creation time (in `try_resolution()`,
  `find_rewrites()`, etc.), capture the unifier's bindings before discarding it. The unifier
  already computes this; we just need to save it.
- **`src/prover/proof.rs`**: Replace the per-rule cases in `reconstruct_step()` with a single
  generic operation: compose the conclusion var_map with the stored bindings to produce premise
  var_maps.

### Benefits

- `reconstruct_step()` collapses from 500+ lines of per-rule cases to a small generic function.
- No redundant re-unification during reconstruction.
- Easier to add new rule types (just save the bindings; no custom reconstruction needed).
- Easier debugging (can inspect the stored bindings at each step).

### Considerations

- Memory overhead: storing unifier bindings per step. Likely modest since most steps have few
  variables.
- Need to define a clean representation for the stored bindings that works uniformly across
  rule types.
- Step 1 should be done first, since separated simplification means the stored bindings only
  need to describe one operation per step.
- The exact representation of "stored bindings" needs design work. It could be a `VariableMap`
  per premise scope, or something more compact. This should be determined during implementation
  by looking at what the unifier actually produces.
