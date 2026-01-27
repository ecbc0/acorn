---
description: Profile the prover and generate a top-down performance summary
triggers:
  - when the user asks to profile
  - when the user asks about performance
  - when the user wants to know where time is being spent
---

# Performance Profiling Workflow

Use this skill when the user asks to profile the Acorn prover. This generates a top-down summary showing where time is spent.

## Available profiling targets

- `profile_reprove` - Profiles reproving `real.double_sum` module (representative prover workload)
- `profile_reverify` - Profiles reverification

Ask the user which target to profile if not specified.

## Build with frame pointers

Frame pointers are required for accurate call graph profiling. Replace `TARGET` with `reprove` or `reverify`:

```bash
RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=profile_TARGET --profile=fastdev
```

## Record profile with perf

```bash
rm -f perf.data && perf record -g --call-graph fp -o perf.data target/fastdev/profile_TARGET
```

The exit code 1 is expected (the profiled program may exit with error).

## Generate top-down report

Get the inclusive time breakdown (with call graph):

```bash
perf report -i perf.data --stdio --percent-limit 0.5 2>&1 | grep -A 2000 "Samples: [0-9]*K" | head -300
```

Get self-time breakdown for the main event:

```bash
perf report -i perf.data --stdio --no-children --percent-limit 0.3 2>&1 | grep -A 500 "Samples: [0-9]*K" | grep -E '^\s+[0-9]+\.[0-9]+%' | head -50
```

## Output format

Provide a top-down summary showing what logical phases take time. Example for `reprove`:

```
Within Prover::search, the breakdown is:

| Phase                  | % of search |
|------------------------|-------------|
| PassiveSet::simplify   | ~62%        |
| PassiveSet::push_batch | ~19%        |
| ActiveSet::activate    | ~13%        |
| ActiveSet::simplify    | ~6%         |
```

## Guidelines

1. Report components that account for >10% of their parent's time
2. For significant components (>10%), break down what's inside them
3. Focus on the top-down view (what logical phases take time), not bottom-up (individual functions)
4. Identify the main call tree first, then break down each significant phase

## Notes on reprove profiling

For `profile_reprove`, the main phases of the prover are:
- `PassiveSet::simplify` - checking if clauses are subsumed
- `PassiveSet::push_batch` - adding new clauses, building fingerprint index
- `ActiveSet::activate` - generating inferences (resolution, rewriting)
- `ActiveSet::simplify` - forward simplification
