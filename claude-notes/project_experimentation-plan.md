---
name: experimentation-plan
description: "Plan for comparing Specimen-derived generators vs handwritten Cedar generators — metrics, phased runs, targets, variants"
metadata: 
  node_type: memory
  type: project
  originSessionId: 64e435f2-0652-41ee-b7e7-aaa249d451e9
---

Goal: determine if Specimen-derived generators can replace some handwritten Cedar generators.

## Key Differences

| | Specimen | Handwritten |
|---|---|---|
| Choices | PRNG with numeric seed | Parsing from buffer of numbers |
| Overhead | Protobuf + FFI (Lean → Rust) | Generator and target both in Rust |
| Determinism | Unguided only, deterministic per seed | Unguided deterministic per buffer; guided effectively nondeterministic |
| Correctness | Only generates spec-valid inputs (modulo soundness bugs) | Can produce both valid and invalid inputs |

## Metrics

- Throughput (avg tests/sec)
- 2- and 3-path coverage over time
- Source line coverage over time
- Uniqueness (repeat rate)
- Size distribution
- Topmost constructor distribution

## Phased Fuzzing Runs

Phase 1: Measure throughput with minimal instrumentation; record seed/buffer + count N + timestamps.
Phase 2: Re-run the same N inputs with line coverage instrumentation; emit coverage data on improvement.

For guided fuzzers: measure line coverage on the corpus of coverage-improving inputs only (guidance is nondeterministic so same buffer won't reproduce same inputs).

## Line Coverage Measurement

- llvm-cov is heavyweight; plan to emit region coverage from counters directly during runs.
- Use llvm-cov only at end for final line coverage derivation.

## Plotting

- Low R: plot each run as separate line.
- High R: 95% confidence interval for coverage/k-paths over time.

## Guided Specimen (Future)

Requires buffer-parsing generators in Specimen (via Basalt's Generator monad with typeclasses). Would enable direct comparison to guided handwritten fuzzer.

## Targets

1. validation-drt (type-directed and non-type-directed variants)
2. validation-pbt (type-directed and not)
3. symcc-term-drt variants

All realizable with current Specimen generator once full policy generator with scope constraints is complete.

## Specimen Variants to Explore

- Scoring heuristics (some simple ones don't terminate in reasonable time for Cedar)
- Weighting heuristics
- Depth of data unconstrained by relations
- Budget for relation-constrained generators (e.g., well-typed expressions)
- Budget consumption strategy: depth-based vs node-based sizing

**Why:** This is the core internship deliverable — results inform whether Specimen generators are viable replacements.
**How to apply:** Use this context when helping with fuzz target setup, coverage measurement, experiment scripting, or generator tuning.
