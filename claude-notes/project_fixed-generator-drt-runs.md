---
name: project_fixed-generator-drt-runs
description: 5 concurrent EC2 validation-drt runs (2026-08-03) verifying the enum-exclusion + closure generator fix
metadata: 
  node_type: memory
  type: project
  originSessionId: 01c084b2-8df7-4bc5-913e-f57d20956638
  modified: 2026-08-03T23:50:35.021Z
---

On 2026-08-03, after implementing the Path-A schema-generator fix (see below),
launched 5 concurrent `validation-drt` full-deliverable runs on EC2 (dev acct,
profile `cedar-experiment`, us-east-1) — 20 reps × 5 approaches
(`approaches.default.txt`: handwritten + steep-tags/typeof-check sz12/sz20),
all `c7i.48xlarge` (192 vCPU), `ON_FINISH=stop` (paused/reusable after).

Superseded twice. **Current (coverage-enabled) runs, launched 2026-08-03 with the
fused line-coverage feature (SOURCE_COV on by default):**

| run | instance | RUN_SECS = DURATION | SEED_BASE |
|---|---|---|---|
| 30s   | i-0bf95a46b77cc4bfe | 30    | 0    |
| 10min | i-0750be377698c5704 | 600   | 1e12 |
| 1h    | i-03721ca4e49e8af56 | 3600  | 2e12 |
| 4h    | i-00014e8d4a4593c3a | 14400 | 3e12 |
| 12h   | i-02476195895f3418b | 43200 | 4e12 |

(Two earlier coverage-run sets were relaunched away: one carried accumulating profraw,
one had a coverage_compare exclusion leak — `llvm-cov export` filters totals but not
`functions[]`, so generator/harness functions leaked into the set/Jaccard/diff until
coverage_analyze re-applied the ignore regex per-file. Both fixed in the current set.)

**2026-08-03 (later): the above set's coverage pipeline was BROKEN + superseded again.**
The completed 30s run (`ci-run-20reps-30s-20260803T215304Z`) gave good STRUCTURAL results
— specimen beats handwritten on 3-paths with non-overlapping CIs (typeof-check-sz12 360
[352,364] vs handwritten 242 [230,252]), ~10× unique skeletons, and **0 DRT mismatches
over ~2.9M differential validations** (confirms the Path-A schema fix) — BUT
`source_lines_covered=0` everywhere / empty `coverage_compare.json`. Root cause:
`run_experiment.sh` did `export AWS_PROFILE=cedar-experiment`, which does not exist on the
EC2 box (instance role) → every `aws s3 cp` failed, and the Phase-2 post-step `rm -f
*.profraw` ran UNCONDITIONALLY → profraw lost, never in S3.

**Fixes (uncommitted, in the src.tgz packaged 2026-08-03 later):**
1. `run_experiment.sh`: only export AWS_PROFILE when `USE_INSTANCE_ROLE!=1`; else use the
   default cred chain. `user_data_body.sh` sets `USE_INSTANCE_ROLE=1`. Phase-2 post-step
   now deletes profraw ONLY on a *successful* upload (`if aws s3 cp …; then … rm; fi`).
2. **Scope = DYNAMIC per-phase reset** (chose over static call-graph after investigation —
   see below). New `ValidationCov` in `source_cov_tracker.rs`: resets LLVM counters right
   before each `target.run` and folds only that delta into a union; `overwrite_live()`
   writes the union back into the live counters before the final profraw dump. So the
   profraw is VALIDATION-ONLY — generation / k-path analysis / proto encode+decode /
   `Schema::try_from` construction never appear. Wired in `collect.rs` (begin/fold around
   `target.run`, over-time `counters_hit`=`vcov.hit()`, final `overwrite_live()`+dump).
   NumCounters=32356 → per-input scan is ~2s/72k-rep, ~1min/core at 12h (negligible).
   Verified locally: scoped profraw has 0 `cedar_policy_generators` fns, 451 `/validator/`
   fns (>2× the static graph's 198), only the 14 evaluator fns validate genuinely calls.
   `coverage_analyze.py` IGNORE_REGEX simplified (dynamic scope already excludes
   construction; dropping `/validator/schema.rs` would now wrongly drop validate-time
   schema access). End-to-end local smoke: coverage_compare populated, source_lines_covered
   nonzero, all plots emit.

**Why dynamic, not static call-graph:** `cargo-callgraph` (rust-analyzer HIR based, no
dyn-dispatch setting) UNDER-approximates — reachable-from-`validate` = 389 cedar fns but
451 are actually covered (misses ~130 via dyn dispatch); as an exclusion it misclassified
~7 typechecker accessors (principals/resources/attributes) as gen-only. Name-based
over-approx (+131) blunderingly pulls in 45 evaluator fns that validate never calls. So the
call graph is good for IDENTIFYING construction machinery (confirmed 208 gen-only fns) but
not as scope authority. Dynamic per-phase reset needs none of it.

**VERIFIED + RELAUNCHED (final set).** Canary `i-0c726567283054b08`
(`ci-run-20reps-30s-20260803T231704Z`, 30s) confirmed the fix on EC2: coverage_compare
POPULATED, source_lines_covered validator-range (handwritten 5062, specimen 4660-4701;
NOT the ~19k unscoped garbage), Jaccard ~0.83, generator excluded. Also verified via two
local runs (rust-only): a quick handwritten-vs-specimen (Jaccard 0.75) and a **2-min
time-bounded** run (see COLLECT_MAX_SECS below) — specimen uniquely covers extension
typechecking (datetime/decimal parse, typecheck_binary) + diagnostics; handwritten
uniquely covers TEMPLATE slot-filling (`with_filled_slot`) + rbac constraint paths →
concrete "teach specimen templates / combine" signal.

Added `COLLECT_MAX_SECS` (wall-clock stop) + `COLLECT_SKIP_CORPUS` (no per-input file
spray) to `collect.rs` for honest time-bounded runs — set VALID_COUNT huge, time is the
bound. In 120s: handwritten ~700 valid (2% yield, slow gen), specimen sz12 ~137k-171k.

Old broken-coverage set (i-0750.../i-0372.../i-0001.../i-0247...) TERMINATED 2026-08-03.
**Final long runs launched 2026-08-03 (all c7i.48xlarge, ON_FINISH=stop, fixed pipeline):**

| run | instance | RUN_SECS | SEED_BASE | S3 root |
|---|---|---|---|---|
| 30s(canary) | i-0c726567283054b08 (stopped) | 30 | 0 | ci-run-20reps-30s-20260803T231704Z |
| 10min | i-059a36c1f08cc8763 | 600 | 1e12 | ci-run-20reps-600s-20260803T234947Z |
| 1h | i-0b5c1581448987934 | 3600 | 2e12 | ci-run-20reps-3600s-20260803T234953Z |
| 4h | i-032a4db02626829eb | 14400 | 3e12 | ci-run-20reps-14400s-20260803T234959Z |
| 12h | i-0d3b33ab99f0581f9 | 43200 | 4e12 | ci-run-20reps-43200s-20260803T235006Z |

**profraw NEVER accumulates:** fused collect records the over-time series as in-process
region-hit COUNTS (`counters_hit` in snapshots.json, no per-snapshot profraw); writes
ONE final profraw per rep; Phase 2 uploads that final to S3 and `rm`s it locally right
after each rep's collect. coverage_analyze `--from-collect` reads counts locally for the
over-time band and downloads finals from S3 one-at-a-time, merging incrementally
(running profdata + one final) then deleting — so at most ~1 profraw is on disk at once.
Corpus streams to S3 (never local). (Superseded IDs: the i-0ca5.../i-010a.../i-0bf6.../
i-070f.../i-02072... set carried the accumulating code and were terminated.)

(Prior non-coverage set — i-0d02d6a6421ceba9d/i-0e1871c0f0a5519ed/i-0b94702a9802b1bd3/
i-032f6f4bb5b59f324/i-072dfc67bccfcfcd2 — terminated/stopped; superseded by the above.)
These runs carry the coverage pipeline: fused Phase-2 line coverage
(`-C instrument-coverage` collect binary, harness excluded incl. kpath/proto/try_from),
over-time CI bands (throughput / 2-,3-paths / unique / line coverage), and
`coverage_compare.{json,png}` (Jaccard + only-A/only-B by function). See
[[reference_line-coverage-fused-pipeline]] if written.

(Relaunched twice — first to fix `DURATION`, then to give each run a **distinct
SEED_BASE** so the 5 are independent samples, not the same seeds at different lengths.
Only the 30s instance survived from the first relaunch; the other four IDs above are
the final ones. Methodology fixes:
1. **throughput window `DURATION` must equal `RUN_SECS`** — now the default in
   `experiment_scripts/{run_experiment.sh,aws/launch.sh,aws/run_on.sh}` (`DURATION:-$RUN_SECS`).
2. **distinct SEED_BASE per run, provably non-overlapping.** rep *i* uses seeds
   `[SEED_BASE + i*SEED_STRIDE, +N)`; STRIDE=1e9, 20 reps, N≈rate·RUN_SECS (~1e7 even
   at 12h) ≪ STRIDE, so one run spans ~2e10. Bases spaced 1e12 (50× margin) → disjoint
   and reproducible (u64 max ~1.8e19).
Real wall-clock ≈ build (~15min) + throughput (=RUN_SECS) + collect/analyze (~2×RUN_SECS)
≈ 3×RUN_SECS. vCPU limit 1152 = 6×192 c7i.48xlarge, so ≤6 concurrent.)

S3 roots: `s3://__S3_BUCKET__/ci-run-20reps-<secs>s-<UTC-timestamp>/`
(results at `…/results/`, violations at `…/<approach>/rep_NN/violations/`).
All read the same `bootstrap/src.tgz` packaged from the local tree WITH the
uncommitted fix (`package_and_upload.sh`, 2026-08-03).

**The fix under test** (branch `relational-typeof`, uncommitted):
- `CedarGen/Relational/Schema.lean` — Path A: `WfEntitiesGo` topological single-pass
  build + `PickClosedAncestors` store **transitively-closed, irreflexive** ancestors
  drawn only from earlier *standard* entries → enum-exclusion + closure + acyclicity;
  `NotInET`/`AppendET` helpers; freshness (no dup type names).
- `CedarProto/Encode.lean` — encoder now reverses ancestors→descendants for proto
  field 2/3 (`descendants(x)={y|x∈ancestors(y)}`); makes the round-trip faithful
  (verified A→B→C decodes back identically) instead of mirrored.
- `SchemaTest.lean` — `favorAncestors` weight modifier (root-namespace, env.contains
  fallback; NO `initialize registerWeightModifier` — not in scope there): mild flat
  boost `PickClosedAncestors.pick *3+2`, `WfEntitiesGo.standard *2+1`. Edge density
  scales via the `size` parameter, NOT via cranking the multiplier (measured
  869→1255→1734 edges at size 12→24→40; max ancestors 4→7→9).

Local verification (3000 schemas): enum-exclusion / closure / irreflexivity = 0
violations. **Key result to confirm from these runs: DRT mismatches = 0** (the old
generator dumped 14 enum-in-hierarchy mismatches; see [[reference_enum-hierarchy-drt-mismatch]]).
Bug 2 is now ungeneratable at the source. Related: [[reference_specimen-weight-modifier]],
[[reference_functional-to-relational-pitfalls]], [[project_experimentation-plan]].
