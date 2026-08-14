---
name: reference_typeof-check-capmerge-generator-hang
description: Specimen typeof-check CapMerge generator can hang (backtrackFuel explosion); repro seed + systemic timeout fix
metadata: 
  node_type: memory
  type: reference
  originSessionId: 01c084b2-8df7-4bc5-913e-f57d20956638
  modified: 2026-08-01T12:47:32.495Z
---

The `typeof-check` Specimen strategy at `lean-size 20` can hang the **generator**
(not the DRT target, not the typechecker) indefinitely: `Specimen.GeneratorCombinators.backtrackFuel`
grinds through a combinatorial backtracking search in the `CapMerge` rule of the
`TypeOfCheck` variant on a near-unsatisfiable seed. Symptom: 100% CPU one core,
flat ~135 MB RSS, zero output. Confirmed via gdb thread-1 backtrace (stack depth
~134 bounded, top frame moving through `randNat`/`Plausible.Gen.choose` = live search).

Discovered in run `run-10min-20reps` (commit aed5804, branch relational-typeof),
approach typeof-check-sz20, rep_02.

**Exact deterministic repro** (no instance needed): the `lean-schema-typeof` generator
drives an internal `next_seed` from `start_seed`, striding by `policies_per_schema`
(=`CEDAR_BATCH_SIZE`, default 100) per refill; stuck refill seed ≈ `start_seed + valid_consumed`.
rep_02 → start_seed = 2×1e9 = 2_000_000_000; hang near seed **2_000_098_000**.
Replay `generate_schema_typeof_proto({seed, size:20, schema_size:20, strategy:"typeof-check", count:100})`
from 2e9 in steps of 100 with a per-call timeout; first timeout = exact offender, then
bisect within the batch (count:1) for the single term-seed. Full artifact:
`cedar-drt/coverage/GENERATOR_HANGS.md` and `s3://__S3_BUCKET__/run-10min-20reps/findings/HANG-1-typeof-check-capmerge.md`.

**Systemic gap (FIXED):** `run_collection_session` / `run_throughput_rep` called
`generator.generate()` with NO wall-clock guard, so one pathological seed stalled a whole
rep and blocked the experiment's PHASE-2 `wait` forever. Fix shipped:
`cedar-drt/coverage/src/timeout_ffi.rs` — `TimeoutFfi` runs each generation FFI call on a
dedicated worker thread with `recv_timeout`; on timeout it logs `SLOW_SEED <params>`, abandons
the (unstoppable) spinning worker, spawns a fresh one, and returns None so the loop skips to
the next seed. Env: `GENERATE_TIMEOUT_SECS` (default 50), `GENERATE_MAX_ABANDON` (default 16,
`exit(3)` past it). Generators (`lean_gen.rs`) hold `TimeoutFfi` instead of `CedarLeanFfi`.
Safe because `CedarLeanFfi` inits per-thread (module init is `Once`), so leaked Lean-inited
workers coexist fine.

**Timeout must be per-BATCH, not per-policy:** the FFI call generates 1 schema + `CEDAR_BATCH_SIZE`
(=100) policies at once. Measured: most sz20 typeof-check batches finish <1s, but the distribution
has a heavy finite tail — a *legitimate* batch (seed 12500) took **22.4s** — plus true infinite
hangs (10700, 29800). So the timeout must clear the finite tail (hence 50s, not 10s) or it
false-skips real inputs. Contention on the 192-vCPU box is mild (~200 hot threads / 192 cores).
Distinct from [[reference_relational-action-type-soundness-gap]] (that's a soundness/validity
gap; this is a generator liveness/robustness gap).
