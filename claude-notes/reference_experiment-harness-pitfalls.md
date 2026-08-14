---
name: experiment-harness-pitfalls
description: "cedar-experiment binary pitfalls: collect orchestrator drops flags, guided local drain is no-op, lean-typeof size blowup"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 62129ecd-4491-40a1-8da6-3bd72390aff9
  modified: 2026-07-23T17:58:33.423Z
---

Gotchas in `cedar-drt/coverage` `cedar-experiment` binary (throughput/collect/analyze phases). Verify against current code before relying — these were observed 2026-07-23.

## collect orchestrator drops flags
`cmd_collect` multi-rep orchestrator (the `--reps N` path, ~experiment.rs:591) builds child args and **omits `--guided`, `--fuzz-target`, and `--s3-bucket`/`--s3-prefix`**. So `collect --guided --reps 1` silently spawns a child WITHOUT `--guided` → runs the **unguided ABAC PRNG generator** (looks like ~2.3% validity, millions of PRNG attempts), and S3 uploads never happen.
**Workaround:** drive collection with `--single-rep 0` (honors all flags). S3 upload verified working only in single-rep mode.

## guided local collection discards inputs
`run_guided_collection` (non-S3) drains logged inputs from `/dev/shm` with a **no-op callback then deletes them** — nothing is written to the corpus dir. Guided inputs persist ONLY via the S3 `BatchUploader` (single-rep `--guided --s3-bucket ...`). Analyze guided from S3 with `--format fuzz`; Specimen from local with `--format proto`.

## guided valid_count semantics
For guided, `--valid-count` is passed as libfuzzer `-runs=N` (execution count, mislabeled "seconds" in a println). To match a throughput window, set N = the throughput phase's measured exec/total count.

## lean-typeof exponential size blowup
`lean-typeof` (fixed `testEnv`, has tags + rich attrs, amplified by `favorHasTag`) blows up with generation size: ~4600/s at sz5, 2553/s at sz12, 734/s at sz15, 378/s at sz18, and effectively **hangs at the default sz20** (a single attempt takes minutes; not infinite). Use `--lean-size 12` for a healthy rate. `lean-schema-typeof` is unaffected (its generated envs are simpler). See [[experimentation-plan]].
