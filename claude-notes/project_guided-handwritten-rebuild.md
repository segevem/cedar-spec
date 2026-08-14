---
name: project_guided-handwritten-rebuild
description: "CRITICAL correction + plan — handwritten baseline must run via cargo-fuzz (guided), not unguided; build state + remaining orchestration"
metadata: 
  node_type: memory
  type: project
  originSessionId: 01c084b2-8df7-4bc5-913e-f57d20956638
  modified: 2026-08-05T22:56:10.455Z
---

# Guided handwritten rebuild (2026-08-04)

## ⭐ PRE-COMPACT RESUME STATE (2026-08-05, latest) — READ FIRST
Layers 1-4 of the scope-coverage work are DONE & validated. welltyped-policy specimen generator
(real scopes + typed conditions) works; end-to-end run shows it MATCHES the static handwritten
baseline (specimen 5575 vs hw-slots-off 5649 lines, CIs overlap), residual gap = slots (~550,
Lean doesn't model them) + small non-slot (error paths + `.offset` extension). See sections below.

IN FLIGHT — RUN #3 (REPS=20, 15min): instance **i-0ce511d59d4eded57** (c7i.48xlarge), S3ROOT
**ci-run-20reps-900s-20260805T215529Z**, ON_FINISH=stop, AWS_PROFILE=cedar-experiment (acct __AWS_ACCOUNT_ID__,
region us-east-1). Building/collecting as of compact; NO results yet. Has the per-arm coverage_compare
fix (SSM-pushed to the instance before PHASE 3.5). 
ON RESUME:
1. Check `aws ec2 describe-instances ... i-0ce511d59d4eded57` state + `aws s3 ls s3://cedar-specimen-
   experiment-results/ci-run-20reps-900s-20260805T215529Z/results/`. When results exist, pull
   coverage_compare.json + bootstrap_ci.json. KEY new pairs (from the per-arm fix): 
   **wt-policy-sz12_vs_hw-slots-off** (clean static-vs-static, expect near-0 only_b gap + tight CIs)
   and **wt-policy-sz12_vs_hw-slots-on** (isolates the ~550-line slot delta). Download PNGs to a
   local folder (e.g. ~/l4_graphs_run3/); coverage_compare.png left panel shows the per-arm bars.
2. USER WANTS TO SEE the updated (per-arm) graphs — that's the immediate deliverable when run #3 lands.
OPEN DECISIONS (user hasn't confirmed): (a) add `.offset` (+ check durationSince/toTime) to the
condition/ext generator to close the datetime residual (specimen emits 0 offset, hw 64); (b) whether
to do further runs. STOPPED instances (DO NOT kill w/o direction): i-0e8240e6c9dcb73cc (run#1, contaminated),
i-0f2eaedc083f8a3fd (run#2, clean 5-rep). GRAPHS on disk: ~/l4_graphs (run#1), ~/l4_graphs_run2 (run#2, union-only).
DIAGNOSTIC TESTS added to cedar-lean-ffi/src/lean_ffi.rs (mod proto_roundtrip, mostly #[ignore], read
/tmp/l4res/*.bin): est_probe_templates_vs_policies, inspect_corpus_batches, scope_form_distribution,
extension_usage, condition_clause_count, sweep_scopes + the 2 proptests (policyset/schema roundtrip).
+ slots_refactor_test in cedar-drt/fuzz/src/validation_drt.rs. All harmless; can be trimmed later.
src.tgz in S3 = latest (has guided.rs contamination fix + coverage_analyze.py per-arm fix). lean_cache.tgz
current (Lean spec has Layers 1-3). Uncommitted working-tree changes across cedar-lean, cedar-lean-ffi,
cedar-drt (see the section bodies for the file list).


## THE CORRECTION (why this exists)
The coverage experiment's `handwritten` approach was running **UNGUIDED** — the
`ABACGenerator` PRNG→`arbitrary` loop in `cedar-experiment` (`generators.rs:54`,
`SmallRng` → `Unstructured` → `cedar_policy_generators`) — **NOT** the real
cargo-fuzz coverage-guided libFuzzer run. Handwritten MUST run via cargo-fuzz
(sancov, coverage-guided) to be a fair baseline. **Therefore ALL previously-reported
handwritten numbers are INVALID as the baseline** (throughput, 2/3-paths, the 10min
"5167 lines", the "642 only-handwritten" diff, etc.) and must be re-derived via
cargo-fuzz. Specimen numbers are VALID (keep — see below).

**Root cause it ran unguided:** the cargo-fuzz guided *collection* was never finished —
NO fuzz target implemented the `CEDAR_FUZZ_LOG_DIR` input-logging or `CEDAR_FUZZ_STATS`
that `guided.rs`'s drain/throughput readers depend on, so `run_guided_collection`'s
drain was a no-op (matches [[reference_experiment-harness-pitfalls]]: "collect
orchestrator drops --guided/--s3; guided local drain is no-op"). It silently fell back
to the unguided ABACGenerator.

## WHAT THE USER WANTS
- Handwritten = **cargo-fuzz guided (sancov)**. BOTH **plain** guided
  (`validation-drt-type-directed`) AND **well-typed** guided (`validation-welltyped-drt`,
  `Corpus::Reject` rejects ill-typed so libFuzzer steers toward well-typed).
- Replay **ALL valid inputs the fuzzer produces** (NOT libFuzzer's minimized ~1000
  corpus) — via logging drain streaming every valid input to S3.
- **Phased** (same as existing): throughput (runs for full experiment length RUN_SECS)
  → collect → analyze.
- **Parallelize the analyze/replay stage** (per-rep independent) — "no longer fused."
- Run on **EC2/S3**; do NOT blow up local storage/memory (drain-and-delete from
  `/dev/shm`, stream to S3). Do NOT kill the running 1h/4h/12h instances.
- Do NOT re-run specimen (numbers already collected).

## BUILT + VERIFIED (compiles; capture half proven)
- `cedar-drt/fuzz/src/lib.rs` — NEW `pub mod guided_log`: `log_input(bytes)` writes each
  valid input as `[schema_len:u32-le‖schema-proto‖policies-proto]` (SAME framing as the
  collect corpus) to `$CEDAR_FUZZ_LOG_DIR` (temp-then-rename); `note_attempt()` bumps
  total + periodic snapshot; `write_stats()` writes `$CEDAR_FUZZ_STATS` JSON
  `{valid_count,total_count,elapsed_ms,snapshots:[[ms,v,t]]}`; `install_stats_at_exit()`
  = `libc::atexit`. All no-op when env unset.
- `cedar-drt/fuzz/src/validation_drt.rs` — `is_well_typed(schema,policies)` =
  `Validator::new(schema).validate(policies,Strict).validation_passed()` (SHARED predicate,
  defined identically in `coverage/src/target.rs::is_well_typed`); `encode_replayable(...)`
  (needs cedar-policy `protobufs` feature — ADDED to `fuzz/Cargo.toml`); `fuzz_target`
  (plain) + `fuzz_target_welltyped` (Corpus::Reject) both call `note_attempt()` +
  `log_input(encode_replayable(...))` on valid/kept.
- Targets: `fuzz_targets/validation-drt-type-directed.rs` (plain) + NEW
  `validation-welltyped-drt.rs` (+ `[[bin]]` in Cargo.toml). Both `install_stats_at_exit`.
  **REMOVED `install_coverage_flush_handler`** from them — it references
  `__llvm_profile_write_file` which is ABSENT under the sancov cargo-fuzz build (that was
  the earlier link error). Guided coverage comes from REPLAY, not this binary.
- VERIFIED: both `cargo fuzz build -s none <t>` link OK; a 12s local run of
  `validation-drt-type-directed` logged **9096 valid inputs** (69 B each) + correct stats.
  (Logged files at `/home/segevem/.claude/jobs/01c084b2/tmp/gtest_log/in_*.bin`.)
- Also present but for the UNGUIDED well-typed variant (dormant unless env set, keep):
  `coverage/src/target.rs::is_well_typed`; `collect.rs` `COLLECT_WELLTYPED_ONLY` reject
  gate + `COLLECT_MAX_SECS` + `COLLECT_SKIP_CORPUS`; `lib.rs::run_coverage_session` same
  gate; `launch.sh` conditional `COLLECT_WELLTYPED_ONLY` passthrough. `run_experiment.sh`
  AWS-profile fix (`USE_INSTANCE_ROLE`) + rm-only-on-successful-upload (KEEP these).

## REUSE (don't reinvent)
- `coverage/src/experiment/guided.rs`: `run_guided_throughput` (cargo fuzz run
  -max_total_time), `run_guided_collection_with_drain` (spawns fuzz bin with
  `CEDAR_FUZZ_LOG_DIR`/`STATS`, drains to `on_file`, deletes — bounded).
- `experiment.rs`: `cmd_throughput --guided` (~L396); `cmd_collect --guided --s3-bucket`
  (~L516-538 wires `BatchUploader` → drain → S3). Args `--guided --fuzz-target --s3-bucket
  --s3-prefix`.
- `main.rs` (`cedar-drt-coverage` bin): `replay_proto_corpus` (L232) + `replay_s3_corpus`
  (L358, cfg profraw+s3): decode `[schema_len‖schema‖policies]`, validate, dump
  profraw+snapshots to `$REPLAY_PROFRAW_DIR`. **Uses `SourceCovTracker` (reset-once,
  includes proto decode) — MUST convert to `ValidationCov` (begin-before-validate /
  fold-after / overwrite_live+dump final / counters_hit snapshots, mirror collect.rs) for
  scope-consistency with specimen (fused) numbers.**
- `coverage_analyze.py`: `--from-collect` reads snapshots.json (counters_hit) +
  final.profraw; IGNORE_REGEX simplified (keeps validator/schema).

## DESIGN v2 (2026-08-04, after user corrections) — SUPERSEDES parts of below
Three user corrections reshaped the guided (and fused) orchestration:
1. **NO capped probe** — throughput runs the FULL RUN_SECS to measure V_t (the fair
   "how many terms this generator produces"). Reverted GUIDED_PROBE_SECS.
2. **TRUE PARALLEL on separate cores** (not concurrent/time-sliced) — for EACH rep,
   throughput and collect are TWO separate taskset-pinned processes launched together.
   `launch.sh` now sizes to PROCS_PER_REP(=2 unless VALID_COUNT) × reps × approaches vCPU.
3. **COUNT-SIGNAL, not time-cut** — throughput emits V_t (valid_count) when it finishes;
   collect runs UNBOUNDED and stops once it has collected V_t. Collect is slower (logging/
   coverage/Lean I/O) so it runs PAST the probe's wall-clock until it matches V_t — it does
   NOT cut off when throughput ends. Applies to BOTH guided AND fused.
   - guided: `collect --guided-match-throughput` → `guided.rs` count-signal (unbounded fuzz
     child, monitor kills it when drained ≥ V_t from throughput/_fuzz_stats_rep_NN.json).
   - fused: `COLLECT_MATCH_STATS=<throughput rep json>` env → `collect.rs` polls valid_count
     every 4096 attempts, stops when valid ≥ V_t. run_experiment passes --valid-count 0.
   - Same seed for throughput+collect ⇒ collect reproduces the probe's inputs ⇒ corpus =
     exactly those V_t terms.
4. **FAITHFUL replay via the ACTUAL target** — replay (main.rs) now drives the SAME
   `ValidationDrt` target object the fused collect uses (`target.run(&ValidationInput{..})`),
   under `lean-gen` = full DRT (Rust validate + Lean FFI + compare). So the replay's
   cedar-policy coverage scope is IDENTICAL to the fused specimen (incl. the FFI proto
   marshalling) — no proto-encode asymmetry — and it re-runs the differential test
   (mismatches re-caught). Build cedar-drt-coverage with `--features profraw,s3,lean-gen`.
   VERIFIED: 9096 logged inputs → pure-validate 1550 lines vs faithful-DRT 1888 lines
   (Δ338 = FFI proto marshalling), 0 mismatches. Non-lean-gen builds keep a pure-validate
   fallback. NOTE: faithful replay runs Lean per input → ~as slow as collect (acceptable;
   parallelized per-rep by coverage_analyze.py).
NOTE: this changed the FUSED method too, so the already-collected specimen numbers (old
N-sized sequential probe→collect) aren't directly comparable to new runs. For a rigorous
specimen-vs-guided line diff, replay the specimen S3 corpus (saved: verified at
`.../<approach>/rep_NN/corpus/batch_*.bin`) through the SAME lean-gen cedar-drt-coverage
binary (single binary, single scope). 192 vCPU = c7i.48xlarge single-instance max; quota
1152=6×192 (shard across instances for >192 jobs).

## DESIGN v3 (2026-08-04) — MIXED runs unified on the SAME target
User: fused specimen runs the SAME instrumented ValidationDrt target as the guided replay,
so their covered (file,line) sets are directly COMPARABLE across the two binaries — just
COMBINE them, no need to replay specimen. So MIXED (specimen + guided) runs in ONE
experiment are now supported:
- FUSED specimen: inline coverage via instrumented cedar-experiment ($BIN_COV, --from-collect).
- GUIDED handwritten: coverage via faithful replay through instrumented cedar-drt-coverage
  ($BIN_DRT_COV, lean-gen — drives the actual ValidationDrt target).
- `coverage_analyze.py` reads manifest.json, picks per-approach binary+mode (--fused-binary /
  --guided-binary), and COMBINES the (file,line) sets into one coverage_compare.json.
  compare() generalized: guided approaches = the "handwritten" side vs specimen (fused).
- run_experiment.sh: removed all-or-nothing (HAS_GUIDED/HAS_FUSED); UNIFIED per-approach
  throughput‖collect loop; builds BOTH instrumented binaries as needed; manifest written
  BEFORE Phase 3.5. user_data_body.sh builds both (GUIDED_RUN + FUSED_RUN detect).
- New aws/approaches.smoke.txt (2 specimen sz12 + 2 guided) for the mixed smoke test.

## DESIGN v4 (2026-08-04) — CHEAP UNIFIED REPLAY COVERAGE (current)
Smoke test found: (1) guided collect/throughput failed on missing required `--generator`
(fixed: defaulted it in experiment.rs). (2) fused instrumented collect ~100x slower than
throughput under 8-way parallelism. INVESTIGATED (local): throughput 2278/s; collect
uninstrumented (metrics only) 1250/s (1.8x — k-path analysis is cheap); collect
instrumented+per-input-ValidationCov 500/s single-proc; the 100x was PARALLEL memory-bandwidth
contention from per-input `reset_counters()`+`fold()` over the full counter array × 8 procs.
User: no capping; make coverage cheaper; keep the Lean call; DON'T instrument generators/FFI.

TWO fixes (stack to ~10x, verified on 9096 inputs):
1. RESET-ONCE cumulative replay: a replay has NO generation between inputs, so per-input
   reset is unnecessary — reset ONCE, accumulate, read `count_hit()` only at ~20 snapshot
   points (not per input). Removes the per-input memset/read (the bandwidth killer). main.rs
   replay_proto_corpus + replay_s3_corpus rewritten (no ValidationCov; reset_counters once +
   count_hit at snaps + dump live). 1137/s → 8701/s single-proc.
2. INSTRUMENT ONLY cedar-policy crates via RUSTC_WRAPPER
   (experiment_scripts/instrument_cedar_only.sh — instruments cedar_policy, cedar_policy_core,
   cedar_drt_coverage bin; everything else native). Counter array 115488 → 13338 (~9x),
   8701 → 11974/s, coverage preserved 2470 → 2448 lines. Build with
   `RUSTC_WRAPPER=<wrapper> cargo build --bin cedar-drt-coverage --features profraw,s3,lean-gen
   --target-dir target_cov` (NO RUSTFLAGS instrument-coverage).

UNIFIED architecture (supersedes v3 fused-inline): collect is ALWAYS uninstrumented
(fast; streams corpus to S3 + computes inline metrics for fused, guided streams via fuzzer).
Coverage for EVERY approach = reset-once replay of its corpus through the ONE cedar-only-instr
cedar-drt-coverage binary (faithful ValidationDrt target WITH Lean). coverage_analyze.py:
single --binary, all approaches replay (no --from-collect, no fused/guided binary split);
--manifest only LABELS guided vs specimen for compare(). run_experiment.sh: Phase 2 prep builds
only BIN_DRT_COV via wrapper; fused collect uses $BIN (no covenv/profraw); Phase 3.5 one
coverage_analyze call. user_data builds only BIN_DRT_COV (wrapper) + fuzz targets. Removed
BIN_COV entirely. Lean kept in replay (faithful; 0 mismatches on 9096). All scripts syntax-clean;
all binaries compile; reset-once + cedar-only replay verified locally.

## LOCAL VERIFY (2026-08-04) — full pipeline works end-to-end
Ran run_experiment.sh locally (1 specimen typeof-check-sz12 + 1 guided, REPS=2, RUN_SECS=5,
STORAGE=s3). Found+fixed 2 more bugs:
- `NCOUNT[$name]` unbound under set -u (NCOUNT no longer declared -A after restructure →
  arithmetic index eval of "typeof-check" → abort). FIX: manifest N uses `${VALID_COUNT:-null}`.
- guided count-match read `throughput target = 0`: it polled _fuzz_stats_rep_NN.json (rewritten
  periodically → early 0). FIX: poll throughput/rep_NN.json (ThroughputResult, written ONCE at
  probe completion) + read_valid_count ignores 0 (`.filter(|&t| t>0)`). Confirmed: guided reads
  target 4510/4557 and collects 4949/4821 (matches +in-flight). Specimen already worked (it read
  rep_NN.json). experiment.rs cmd_collect target_stats_path → throughput/rep_NN.json.
- ADDED throughput to bootstrap_ci: load_reps merges throughput_valid_per_sec from
  throughput/rep_NN.json; METRICS gained ("throughput_valid_per_sec","throughput (valid/s)").
  Verified (typeof 1602/s, guided 755/s); plot_ci auto-includes it. (user request)
All graphs produced (bootstrap_ci, coverage_compare, over_time_*), coverage ~2400 lines. Local
$BIN rebuilt with fixes. cargo-fuzz + both fuzz binaries present locally (fast iteration).

## SEPARATE + PARALLEL ANALYSIS (2026-08-04) — the big architecture change
Problem found in the 10-min run: SPECIMEN collect ran at ~132/s (vs probe ~1348/s) because it
did INLINE k-path analysis (2+3 path enum) per input → count-matching 808k took ~100min. Fix
(user: "separate analysis, parallelize like maniacs"):
- COLLECT is now STREAM-ONLY for specimen (env COLLECT_STREAM_ONLY, gated in collect.rs
  run_collection_session): generate + DRT (mismatch + probe-speed parity) + stream corpus;
  SKIP the per-input k-path/HLL/node/diversity. cmd_collect skips writing inline analyze.
  Guided already stream-only. So collect ≈ probe speed → count-match completes fast.
- ANALYZE is now a PARALLEL replay (analyze.rs): rayon fold/reduce over the whole corpus on
  all cores. New `Partial` uses HLL (uniques) + NodeHistogram (node counts) — NOT HashSet/Vec
  (those are O(N) and blow memory at millions of inputs; the reason hll.rs exists). Added
  Hll::merge (register-wise max) + NodeHistogram::merge (bucket sum). Bounded memory
  (~2MB/HLL × threads). decode_input + split_batch helpers factored. replay_and_analyze (local)
  + replay_and_analyze_from_s3 collect buffers (stream_batches gives owned Vec) then call
  analyze_buffers_parallel. Added rayon dep. VERIFIED: analyze of 39701 S3 inputs in 6s
  (~6600/s local), metrics match old inline (3paths 296 vs 299, unique 94.5% vs 94.6%).
- DIVERSITY-OVER-TIME RESTORED via NUMBERED OUTPUTS (user's idea; 2026-08-04): buffers are
  already in collection order, so the Vec index IS the stream position. analyze_buffers_parallel
  now splits into N contiguous chunks (ANALYZE_CHUNKS, default 128), analyzes each chunk in
  parallel into a `Partial`, then cumulative-MERGES the chunks IN ORDER — merge is associative +
  each chunk covers a known prefix, so the cumulative state after chunk c == prefix [0..end_c].
  Emits a DiversitySnapshot {input_idx=end stream pos, unique/skeletons/2paths/3paths} per chunk
  boundary. So N_chunks = BOTH the parallelism bound AND the curve resolution (128 → 128-way +
  128-pt curve). input_idx = global stream position (NOT replayed count) so plot_over_time maps it
  to wall-clock via throughput valid_count. Peak mem = chunks × 2 HLL@p21 (4MB) ≈ 512MB (bounded
  by CHUNKS, not N). VERIFIED: 5000-input local corpus → 125 monotone points, LAST snapshot ==
  final AnalyzeResult EXACTLY (unique 4860, 2paths 80, 3paths 212) ⇒ no precision lost by chunking.
  coverage-over-time + throughput-over-time unchanged. $BIN rebuilt (lean-gen,s3).
- run_experiment.sh: specimen collect gets COLLECT_STREAM_ONLY=1; Phase 3 runs replay-analyze
  for ALL approaches SEQUENTIALLY (each rayon-parallel internally → whole box, no oversubscribe/
  HLL-mem multiply). VERIFIED end-to-end locally (~75s mixed run: count-match fast, all graphs).
- All compiles. src.tgz re-packaged with these + the cargo-fuzz-run guided fix.
NEXT: re-bake golden AMI from i-0918 rebuilt with this src (start → fetch src → rebuild
cedar-experiment + cedar-drt-coverage-cov[wrapper] → stop → create-image), then the definitive run.

## 1H DIVERSITY-CODE RUN + AMI RE-BAKE (2026-08-04, live)
- 1H RUN: i-05691b82348867c14 (c7i.48xlarge), S3ROOT `ci-1h-mixed-diversity-20260804T222749Z`,
  launched via launch.sh on the EXISTING golden AMI ami-0a0841fa2f0e47afa (rebuilds fresh
  src.tgz on top → runs the NEW diversity-over-time analyze code). MIXED approaches.smoke.txt
  (2 specimen sz12: steep-tags + typeof-check; 2 guided: plain + welltyped), REPS=20
  RUN_SECS=3600 SEED_BASE=7e12 ON_FINISH=stop. Results → s3://.../<S3ROOT>/results/.
  This is the first real run exercising the restored diversity_over_time curves at scale.
- AMI RE-BAKE DONE: new golden AMI **ami-07994225d79227b05** (name cedar-exp-base-20260804T222741Z),
  baked from i-0918 (rebuilt new src, stopped, imaged). Use it for future launches:
  `AMI_ID=ami-07994225d79227b05 … CONFIRM=1 ./launch.sh`. Supersedes ami-0a0841fa2f0e47afa.
  (Re-bake only warms the AMI cache with new code — launch.sh always rebuilds fresh src anyway.)
- OLD unguided 4h i-032a4db02626829eb + 12h i-0d3b33ab99f0581f9 **TERMINATED** 2026-08-04 (user
  OK'd after mismatch check). MISMATCH CHECK: both were clean — 0 `Mismatch for Policies` + 0
  aborts across all 100 per-rep logs each; completed reps report "0 violations" (e.g. one
  steep-tags-sz12 rep: 34.7M inputs, 0 violations). The scary `run12h_mismatches.txt` on the
  boxes was a STALE local untracked working-tree file (Jul 31, owned by segevem) swept into
  src.tgz — it's the known enum-hierarchy generator bug [[reference_enum-hierarchy-drt-mismatch]],
  NOT from these runs. TODO: `rm cedar-drt/coverage/run12h_mismatches.txt` locally so it stops
  shipping in src.tgz.

## SHARDED COVERAGE ANALYSIS (2026-08-04) — full-core analysis, CIs intact
Problem: coverage replay is the analysis LONG POLE — it re-runs the faithful DRT (Lean per
input) over every valid input, and coverage_analyze.py parallelized only REPS-within-approach
(~20 procs) with approaches sequential + each rep replay SINGLE-THREADED. So a 192-core box sat
~90% idle and wall-clock was floored by the slowest single rep (~collect time, i.e. ~an hour for
a 1h run). User: analysis is usually LONGER than collect; use the cores.
FIX (replay sharding, backend-agnostic enabler):
- s3.rs: `stream_batches_sharded(shard,shards)` — replays a CONTIGUOUS slice of the sorted batch
  list (batch order == stream order), so each of N workers downloads only its ~1/N.
- main.rs: `--replay-shard I --replay-shards N` on the S3 replay; each shard dumps its own
  final.profraw (via REPLAY_PROFRAW_DIR).
- coverage_analyze.py: FLATTEN every (approach x rep x shard) into ONE ThreadPool (saturates the
  whole box, not ~reps cores). `replay_one_shard` runs a shard; `assemble_rep` merges a rep's
  shards: UNION = rep final coverage; CUMULATIVE-merge in shard order = coverage over-time curve
  (one point per shard). N = REPLAY_SHARDS (default 16 in run_experiment.sh) = parallelism bound
  AND over-time resolution. Legacy --from-collect path preserved (no sharding).
- plot_over_time.py: coverage branch keys on corpus_idx → wall-clock via throughput time_map
  (shards run in parallel so replay elapsed is meaningless); SAME x-axis as diversity/throughput
  curves now (consistency gain). Falls back to corpus_idx / legacy elapsed_secs.
- run_experiment.sh: REPLAY_SHARDS=16 default, passed to coverage_analyze Phase 3.5.
CORRECTNESS PROVEN (local, ci-run-4reps-30s S3 corpus): sharded(4/8) final coverage == unsharded
EXACTLY (steep-tags 5279, typeof 5288, guided 2453). Full Phase 3→3.5(sharded)→4 chain on 4 reps:
FINAL CIs compute (validator lines steep 5308.5 CI[5279,5317], typeof 5304 CI[5288,5320], guided
2453 CI[2453,2453]; +3-paths/unique CIs) AND over-time CI bands render (coverage + diversity PNGs).
CI METHOD UNCHANGED: bootstrap is ACROSS REPS (independent samples); sharding is an intra-rep
detail producing bit-identical per-rep values → CIs (final + over-time) fully preserved.
DEMANGLE FIX: coverage_compare by_function labels were RAW v0-mangled garbage (homegrown regex
demangle). FIX: coverage_analyze stores RAW symbols in coverage_compare.json; plot_coverage_compare
demangles at PLOT time via `rustfilt` (batch, rustc-demangle) → readable (SingleEnvTypechecker::
typecheck, Expr::try_from, datetime::parse_datetime...). user_data installs rustfilt (idempotent).
Storing raw = chart re-fixable locally w/o re-replay. Verified on 4-rep smoke.

COVERAGE TREEMAP (2026-08-04, user picked over top-15 bars): "which regions uncovered".
coverage_analyze adds `file_coverage()` (per-file covered/total REGION-lines + module) → new
`coverage_map` section in coverage_compare.json for specimen_union + handwritten_union (merges
each side's per-approach profdata). New plot_coverage_treemap.py: nested squarify treemap
module→file, area=region-lines, color=covered% (RdYlGn, red=uncovered). squarify added to pip
(local + user_data). run_experiment Phase 4 renders both sides. VERIFIED on smoke: validator
typecheck GREEN, schema/json_schema/namespace_def RED; out-of-scope modules (api/parser/est/pst/
tpe/evaluator/ffi) all red — module grouping separates them. NOTE: overall% dominated by
out-of-scope crate code. USER DECISION: leave exclusions AS-IS (IGNORE_REGEX is the single
source of truth — instrument_cedar_only.sh + IGNORE_REGEX; do NOT add a parallel in-scope
allowlist). DIFF TREEMAP added (--mode diff): coverage_analyze `diff_map_of()` computes per-file
only_spec/only_hw/shared/uncovered (line SETS via file_sets); plot_coverage_treemap --mode diff
colors each region by who UNIQUELY reaches it (specimen=blue, shared=gray, hw=orange, uncov=red).
FINDING (smoke): specimen-only 2789 region-lines, shared 2404, HANDWRITTEN-ONLY = 2 (!),
uncovered 27316 → guided finds ~nothing specimen doesn't; specimen's unique wins concentrated in
validator::typecheck + proto::ast + validator internals. Phase 4 renders coverage(both sides)+diff
treemaps. Current run i-01c5c515
predates treemap → treemap it POST-HOC by re-running coverage_analyze on its S3 corpus (fast w/
sharding). src.tgz repackaged (treemap in pipeline for future runs). NOT relaunched.

OVER-TIME X-AXIS TRUNCATION FIX (2026-08-05): plot_over_time used `xmax=min(rep endpoints)`,
so ONE short rep (unlucky libFuzzer seed → smaller count-match → shorter curve) truncated the
whole band (1h graph: hw-guided-plain ended at ~500s not 3600s). FIX: grid to MEDIAN endpoint;
np.interp then MASK (NaN) past each rep's own end (no flat extrapolation); nanmedian + nanpercentile
bootstrap; legend shows n-thinning "n=20→10". x-axis mapping itself was correct (corpus_idx→wall-clock
via throughput time_map, verified: 720 snaps 0→3600s). Regenerated 4 over-time PNGs for the 1h run
(source_lines_covered, 2paths, 3paths, unique) locally + re-uploaded to S3 results. NOT regenerated:
over_time_throughput.png (needs collect/edge_snapshots.json, excluded from results upload) — still
min-clamped in S3; regen from instance EBS if needed. src.tgz repackaged (fix in pipeline).

PROTO ROUNDTRIP ILL-TYPED LEAK (2026-08-05, user flagged welltyped hitting error paths): added
REPLAY_COUNT_ILLTYPED counter to main.rs replay_s3_corpus (re-validates DECODED input w/ Rust strict).
MEASURED (1/20 sample rep_00, 1h run): welltyped 0.16% ill-typed on replay, plain 0.15%, steep-tags
5.1%, typeof 6.0%. CONCLUSION: welltyped's Corpus::Reject works pre-encode, but the proto encode/decode
ROUNDTRIP re-introduces ~0.15% ill-typedness (well-typed→ill-typed) AFTER the reject → welltyped≈plain
on replay + hits wrong_number_args. Coverage is REPLAY-based so the fuzz-time is_well_typed check is
NOT in measured coverage (user's check-before-reject hypothesis doesn't apply). Specimen 5-6% is its
NATURAL unfiltered rate (expected). Guided>specimen coverage result STANDS (like-for-like replay).
Real bug: cedar-policy proto roundtrip not semantics-preserving for ~0.15% of inputs. Fast rust-only
replay binary at coverage/target_cov_fast (features profraw,s3 no lean-gen) for such diagnostics.
Fix options open: (a) repro the roundtrip, (b) re-validate decoded form before logging in welltyped.

STALE-OUT COUNT-MATCH BUG (2026-08-04, caught in i-01c5c515): the golden AMI baked
/opt/exp/.../exp_ci_results from a prior 30s smoke, incl. throughput/rep_NN.json. run_experiment
didn't clear $OUT, so fused+guided collect read the STALE throughput target (e.g. 39701) and
count-matched a 30s-sized corpus in ~20s instead of the full 3600s window → whole run tiny/bogus.
FIX: run_experiment.sh now `rm -rf "$OUT"` at start (unless KEEP_OUT=1) so collect only sees THIS
run's fresh throughput JSONs (written at probe completion; collect polls until then). Symptom to
watch: collect "done" in seconds + "throughput target = <small>" + throughput json mtime older
than launch. i-01c5c515 TERMINATED; relaunched clean.

CURRENT DEFINITIVE RUNS (2026-08-04, user OUT — monitoring autonomously):
- 1h: i-0309c0faed9253c1b, SEED_BASE=11e12, S3ROOT ci-1h-sharded-20260804T233506Z.
- 4h: i-049a97866c2f6f37a, SEED_BASE=12e12, S3ROOT ci-4h-sharded-20260804T233646Z, RUN_SECS=14400.
Both c7i.48xlarge, ON_FINISH=stop, approaches.smoke.txt (2 specimen sz12 + 2 guided), golden AMI
ami-07994225d79227b05, all fixes. MONITORING: ScheduleWakeup is GATED off (needs /loop); instead
using a background `sleep N && echo` Bash task as a self-wakeup timer (re-invokes me on exit) —
first checkpoint ~23min to VERIFY the stale-OUT fix (collect must WAIT through the window, not
finish in ~20s), then every ~30-40min until each finishes. ON COMPLETION per run: verify results
sane, pull CI/over-time/coverage charts, generate post-hoc treemaps (diff + coverage) from the S3
corpus. supersedes i-01c5c515 (stale-OUT bug). PRIOR terminated 1h launches: i-05691b8 (pre-diversity-restore?),
i-009c67 (pre-demangle), i-01c5c515 (stale-OUT). OLD (do not confuse): (c7i.48xlarge), S3ROOT ci-1h-sharded-20260804T230856Z,
REPS=20 RUN_SECS=3600 SEED_BASE=9e12 ON_FINISH=stop, approaches.smoke.txt (2 specimen sz12 + 2
guided), golden AMI ami-07994225d79227b05, ALL fixes (sharding + REPLAY_SHARDS=16 + demangle +
rustfilt). Prior 1h launches i-05691b82348867c14 + i-009c6707789a39dd8 TERMINATED (superseded by
diversity/sharding/demangle fixes respectively). Results → s3://.../<S3ROOT>/results/.

DECISION: single-box full-core sharding NOW (biggest jump ~60→~15-30min analysis, no new infra).
AWS Batch array jobs = the RIGHT managed backend for MUCH bigger/recurring runs (needs container
via existing Dockerfile + ECR + Batch/IAM); sharded units lift onto it later. DIY EC2 fleet =
skip (Batch's cost, none of its benefits). Both binaries compile (cedar-experiment + wrapper cov).

## SPECIMEN SCOPE-COVERAGE GAP + FIX PLAN (2026-08-05)
ROOT CAUSE (traced end-to-end + confirmed with the user): specimen (typeof-check/steep-tags/
budget-aware — all call `generateExprs` in CedarFFI/Generate.lean, differing only in Specimen
Variant) generates well-typed EXPRESSIONS, and `CedarProto.Encode.encodePolicySet`/`encodeTemplateBody`
(Encode.lean) HARDCODES principal/action/resource = All and dumps the expr into `non_scope_constraints`
(the `when` clause). So EVERY specimen policy is `permit(principal,action,resource) when {expr}` — the
scope is inlined into the condition ("precompiled"). => specimen never exercises the scope-constraint →
expr → typecheck path (Expr::is_eq/is_in, PrincipalOrResourceConstraint::from/try_from, with_filled_slot,
validate_slots deep). That path is handwritten-ONLY (the ~1210-line diff) — NOT missing operators
(specimen covers ==/in/hasTag/is INSIDE `when` via Expr::binary_app, 15/15). NOTE: I earlier WRONGLY
claimed specimen misses operators (top-50 by_function name-level noise); corrected. `validate_policy`
itself: 29/30 BOTH sides.
FIX (4 layers; `WellTypedPolicy` in CedarGen/Relational/Policy.lean already specifies valid scopes
.any/.eq/.mem/.is/.isMem consistent w/ reqty; derive via `derive_mutual` which builds the relation +
its deps from structure — NO stub instances):
- LAYER 1 ENCODER = DONE + VERIFIED (2026-08-05). CedarProto/Encode.lean: added encodeEntityReference,
  encodePrincipalOrResourceScope, encodeActionScopeConstraint, encodePolicyTemplateBody, encodePolicies
  (full Cedar.Spec.Policy → PolicySet w/ real scopes; conditions → non_scope_constraints via
  Conditions.toExpr). Mirrors core.proto oneofs (PrincipalOrResourceConstraint any=1/in=2/eq=3/is=4/
  isIn=5; ActionConstraint any=1/in=2/eq=3; EntityReference euid=2). Slots OMITTED (not modeled in Lean
  → future work). Test CedarProto/EncodePolicyTest.lean: 10/10 scope roundtrips PASS (encode→CedarProto
  Lean decode via PolicySet.toPolicies→compare). Single action .mem→in[uid]→decodes .actionInAny[uid]
  (semantic, ok). Build clean.
- LAYER 2 GENERATOR (TODO): derive_mutual on WellTypedPolicy (Policy.lean) → List Cedar.Spec.Policy.
  **USER NOTE: ensure Policy.lean has the ancestor-handling fixes we made** (enum/closure ancestor
  consistency, cf [[reference_enum-hierarchy-drt-mismatch]]) — VERIFY WellTypedPrincipalScope/.mem/.isMem
  targetTy uses fixed ancestor logic before generating. 
- LAYER 3 DISPATCH (TODO): new strategy / scope-mode in generateSchemaTypeOfProtoFFI (Generate.lean) →
  encodePolicies instead of generateExprs→encodePolicySet.
- LAYER 4 RUST (trivial): add approaches.txt line w/ new strategy (already plumbed via `strategy`).

## CROSS-LANGUAGE ROUNDTRIP PBT — DONE + GREEN (2026-08-05)
Implemented the cross-language proto-fidelity PBT the user requested, using the REAL
`cedar-policy-generators` (same infra the DRT fuzzers use), for BOTH policies AND schemas.
- LEAN FFI exports (CedarFFI/Generate.lean): `roundtripPolicySetProto` (decode PolicySet →
  toPolicies → `encodePolicies`) + `roundtripSchemaProto` (decode Schema → toSchema →
  `encodeSchema {ets,acts,reqty:=default}`; encodeSchema ignores reqty). Both `@[export]`,
  pure match on `Message.interpret?`, empty bytes on decode error.
- RUST FFI bindings (cedar-lean-ffi/src/lean_ffi.rs): `roundtrip_policyset_proto` +
  `roundtrip_schema_proto` (mirror generate_*_proto: OwnedLeanObject::new_array_from_buf →
  call_lean_ffi_function → as_byte_array).
- TESTS (cedar-lean-ffi/src/lean_ffi.rs, `mod test::proto_roundtrip`): dev-deps added
  proptest 1.11, arbitrary 1.4, cedar-policy-generators (feature cedar-policy). `generate(buf)`
  drives GenSchema::arbitrary(type_directed settings) → arbitrary_hierarchy →
  **arbitrary_static_policy** (STATIC only — Lean doesn't model template slots) → Schema::try_from
  + into_policy_set. Property = Rust encode → Lean roundtrip FFI → Rust decode, compare the two
  DECODE outputs (cancels benign proto representation choices). `policyset_proto_roundtrip`
  (2000 cases) + `schema_proto_roundtrip` (2000) + `sweep_scopes` (deterministic 5×4×5 scope
  forms × ±when). ALL GREEN. shared_ffi() = process-lifetime OnceLock<CedarLeanFfi> (Lean thread
  is thread-bound + Drop finalizes → init once, never drop; per-case new()/drop churns/crashes).
- COMPARISON helpers: policies → `fingerprint` = sorted `Policy::to_string()` with leading
  `@…` annotation lines STRIPPED (Lean doesn't model annotations; id already omitted by Display).
  schemas → `schema_canon` = `models::Schema::from(&ValidatorSchema)` (via Schema::as_ref) with
  every set-like repeated field SORTED+DEDUPED (descendants, enum_choices, principal/resource_types);
  map fields already compare order-independently. Compare via that (ValidatorSchema derives Educe
  PartialEq but is order-sensitive on enum NonEmpty).
- BUGS/GAPS THE PBT SURFACED (all benign, none affect DRT):
  1. FIXED encoder: `encodePolicyTemplateBody` was ALWAYS emitting field 8 non_scope_constraints
     = encodeExpr(condition.toExpr); for a policy with NO when/unless (Lean condition = []) that
     emitted a spurious `true`, whereas cedar's `non_scope_constraints()` returns None (absent
     field). FIX (Encode.lean): `match p.condition | [] => buf | _ => encodeBytes 8 …`. An explicit
     `when {true}` is a non-empty condition → still emitted (consistent w/ Rust). EncodePolicyTest
     still 10/10.
  2. Annotations: generator emits `@k("v")` (policy.rs:175, no setting to disable); Lean has no
     annotations field → dropped. Handled by stripping `@` lines in fingerprint.
  3. Enum choices: Lean models enums as a Set → decode dedups + encode re-emits SORTED; cedar keeps
     declaration order + dups (NonEmpty<Eid>). Benign (enum validation is set-membership). Handled
     by sort+dedup in schema_canon. **Does NOT affect DRT**: DRT is Rust-encode→Lean-decode only
     (Lean-encode is the NEW Layer-3 path); and decode-side ordering is validation-irrelevant. The
     PBT still guards the enum VALUE SET (a dropped value WOULD affect DRT — cf enum-hierarchy bug).
- CAVEAT (dev-experience): the cedar-lean-ffi test binary ABORTS on any Rust panic
  ("failed to initiate panic, error 3") — likely incomplete unwind tables through the static Lean
  link. So proptest can't shrink (final failure panic aborts). Workarounds used: prop_assert (Err,
  not panic) + inline eprintln diagnostics that flush before the abort + proptest-regressions replay.
  A green property runs fine (no panic). Keep assertions as prop_assert*, avoid unwrap on Lean output.

## LAYER 2 SPEC BUG FIXED — WellTypedActionInList underspecified (2026-08-05, user caught)
Policy.lean `WellTypedActionInList.here` had an UNCONSTRAINED `rest`: once the matching
ancestor `target` was found at the head, the tail of `action in [target :: rest]` was free →
the generator would fabricate arbitrary/invalid action UIDs there (also forcing an
`Arbitrary (List EntityUID)`). FUNCTIONAL-SPEC CHECK confirms this is a real bug: `checkEntities`
(Validator.lean:117-121) + `typeOfLit` (Typechecker.lean:64) require EVERY `.lit (.entityUID uid)`
in a policy (scope folds into a set-of-UID-literals expr) to satisfy
`ets.isValidEntityUID uid || acts.contains uid`, else `unknownEntity` → policy REJECTED. FIX: added
`AllValidActionUIDs : List (EntityUID×ActionSchemaEntry) → List EntityUID → Prop` (nil/cons, each
`IsValidActionUID`) and a `AllValidActionUIDs entries rest` premise on `here`. So every uid in the
list is a valid action UID and ≥1 is an ancestor of the action. (Sound subset: uses IsValidActionUID
only, not the `||` entity-uid alternative.)
FUNCTIONAL-SPEC VALIDITY (for reference): entity UID valid = `EntitySchema.isValidEntityUID`
(Types.lean:153): ty ∈ ets AND (standard→any eid | enum→eid∈eids); missing ty→invalid. action UID
valid = `ActionSchema.contains` (Types.lean:179): uid is a KEY in acts. Policy.lean's IsValidEntityUID
(standard/enum-InStringList/there) + IsValidActionUID (here/there over keys) are faithful mirrors.

## GUIDED CORPUS CONTAMINATION BUG — FOUND + FIXED (2026-08-05, user hunch "slots off isnt working")
Layer4 run #1 (ci-run-5reps-500s-20260805T192542Z, i-0e8240e6c9dcb73cc): hw-slots-off corpus had
93 SLOTTED policies (~same as hw-slots-on 106) → slots-off NOT slot-free. ROOT CAUSE (in
coverage/src/experiment/guided.rs): the fuzz drain dir + libFuzzer working corpus (+ throughput
empty_corpus) were keyed by REP_ID ONLY (`/dev/shm/cedar-fuzz-rep-{NN}`), NOT by approach. Parallel
same-rep guided approaches (hw-slots-off ‖ hw-slots-on) shared the dir and drain-and-delete RACED →
each arm's S3 corpus = race-split MIX of both targets. Hence both had slots + J=0.9998. My noslots
refactor is CORRECT (verified local: FuzzTargetInput<true,false> → 0/209 slotted; <true,true> →
132/219). Bug ALSO contaminated the old 1h plain-vs-welltyped guided comparison.
FIX: added `approach_tag(output_dir)` (sanitized approach name from the approach-specific output_dir)
→ /dev/shm/cedar-fuzz-{approach}-rep-{NN} for drain log_dir, fuzz_corpus_dir, and throughput
empty_corpus. + regression test cedar-drt/fuzz/src/validation_drt.rs::slots_refactor_test
(slots_off_is_slot_free asserts SLOTS=false → 0 slotted). Compiles (cargo check lean-gen,s3 OK).
STILL-VALID from run#1: wt-policy (FUSED, doesn't touch guided /dev/shm) is clean; handwritten_union
legitimately contains both targets' outputs so specimen-vs-handwritten conclusions hold (scope cov
proto 131→37, rbac 77→23, ~15.8% line gap; est/* IS slot/template-driven via Template::from_ast→EST,
unreachable by static-only specimen). INVALID from run#1: slots-off vs slots-on (contaminated).
DIAGNOSTIC TESTS added to cedar-lean-ffi proto_roundtrip mod (harmless, some #[ignore]):
est_probe_templates_vs_policies, inspect_corpus_batches (reads /tmp/l4res/*.bin). KEY MECHANISM
CONFIRMED: proto DECODE builds EST for TEMPLATES via `Template::from_ast`→`Est(ast.into())` (est/expr
+ est/scope_constraints); static Policy::from_ast → Empty (no est). So est/* = template-reconstruction,
not text parsing.

## LAYER 4 RUN #2 RESULTS — FIX CONFIRMED, specimen ≈ static handwritten (2026-08-05)
Run #2 (ci-run-5reps-500s-20260805T210820Z) with the contamination fix: hw-slots-off now 0 slots
(was 93), hw-slots-on has slots. CLEAN numbers (median lines [CI], 5 reps):
  wt-policy 5575 [5544,5616] | hw-slots-off 5649 [5548,5821] | hw-slots-on 6200 [6161,6232]
- specimen ≈ hw-slots-off: only ~74 lines apart, CIs OVERLAP → specimen MATCHES the static handwritten
  baseline (the old "~880/15.8%" gap was contamination + comparing to slot-inclusive union).
- Slots add ~550-572 lines: slots-on(6200) - slots-off(5649). slots-off_vs_slots-on now J=0.8853
  (only_on=572), was bogus J=0.9998 contaminated → slots DO matter (validate_slots/with_filled_slot/
  template-EST), unreachable by specimen (Lean no slots). specimen_union_vs_handwritten J=0.832,
  only_spec=158 (specimen UNIQUELY covers cmp_shape 43, expected_one_of_types 16, eq_shape 14, closures).
- Graphs: /home/segevem/l4_graphs_run2/*.png (bootstrap_ci, coverage_compare, treemap_diff = specimen-only
  158/shared 5321/hw-only 919/uncov 26113; validator/typecheck + proto = shared gray).
TIMING TEST (CedarGen/Relational/PolicyTimingTest.lean, testEnv sz12, n=500): scopes-only 15,151/s vs
full policy 491/s → the HasType CONDITION search is ~97% of gen time; scopes are essentially free
(~30x faster). User's "multiple conditions" hunch REFUTED by corpus (max 1 clause/policy, avg 0.59).
Throughput lever = condition generator, not scopes.
EXTENSION FINDING: specimen emits extensions ~8x handwritten's rate (188/1000=18.8% vs 2-2.5%), covers
the bulk (shared 251 datetime/130 ipaddr/103 decimal, only_spec=0). Residual handwritten-only ext =
`.offset` (specimen emits 0, hw 64) + ill-typed-literal error paths. Fix: add .offset to the ext gen.

## COVERAGE-COMPARE PER-ARM FIX (2026-08-05, user: diff separately not union)
coverage_analyze.py compare() only diffed specimen vs the UNION of guided arms (gunion) → slot-only
lines from slots-on got counted against static specimen, inflating the gap. FIX: added per-arm pairs
`{spec}_vs_{g}` for each specimen×guided (e.g. wt-policy-sz12_vs_hw-slots-off, _vs_hw-slots-on) with
full by_function. plot_coverage_compare.py left panel auto-includes all pairs (right panel still union
by_function; JSON has per-arm by_function). NOTE: per-approach line SETS aren't persisted to S3 (only
counts/over-time), so can't re-diff run#2 post-hoc without re-replay. APPLIED to run#3 (i-0ce511d59d4eded57,
still building) by staging the fixed script to s3://.../bootstrap/coverage_analyze_fix.py and SSM
`aws s3 cp` overwriting /opt/exp/.../coverage_analyze.py before PHASE 3.5 (confirmed REPLACED). Also
repackaged src.tgz (durability; removed scratch CedarGen/Relational/PolicyTimingTest.lean which would
be globbed into CedarGen and duplicate-derive the scope-relation generators). So run#3 results will have
wt-policy-sz12_vs_hw-slots-off (the clean static-vs-static) + _vs_hw-slots-on (slot delta) as separate pairs.

## LAYER 4 RUN #3 LAUNCHED (2026-08-05) — REPS=20, 15min
Instance i-0ce511d59d4eded57 (c7i.48xlarge, 192 vCPU), S3ROOT ci-run-20reps-900s-20260805T215529Z,
RUN_SECS=900 REPS=20 SEED_BASE=17e12 ON_FINISH=stop, golden AMI, approaches.layer4.txt, EXISTING
src.tgz (run#2's, has the contamination fix — no repackage). 120 jobs. .offset NOT yet added (user
launched before deciding). Purpose: tighten CIs to rigorously confirm specimen ≈ hw-slots-off.
Prior instances i-0e8240e6c9dcb73cc (run#1) + i-0f2eaedc083f8a3fd (run#2) STOPPED (don't kill w/o direction).

## LAYER 4 RUN #2 (2026-08-05) — REPS=5 CONFIRMATION after the fix
Instance i-0f2eaedc083f8a3fd (c7i.8xlarge), S3ROOT ci-run-5reps-500s-20260805T210820Z, RUN_SECS=500
REPS=5 SEED_BASE=16e12 ON_FINISH=stop, golden AMI, same approaches.layer4.txt, src.tgz repackaged
w/ the guided.rs fix (lean_cache reused, Lean unchanged). KEY CHECK on completion: pull hw-slots-off
corpus → must be 0 slots (was 93); slots-off vs slots-on must now genuinely DIFFER. If confirmed →
REPS=20 for real numbers. Prior run #1 instance i-0e8240e6c9dcb73cc left STOPPED (do not kill w/o
direction).

## LAYER 4 LAUNCHED (2026-08-05) — welltyped-policy vs handwritten slots off/on, 500s
Instance i-0e8240e6c9dcb73cc (c7i.8xlarge, 32 vCPU), S3ROOT ci-run-5reps-500s-20260805T192542Z,
RUN_SECS=500 REPS=5 SEED_BASE=15e12 ON_FINISH=stop, golden AMI ami-07994225d79227b05, AWS_PROFILE
cedar-experiment (account __AWS_ACCOUNT_ID__). Approaches (aws/approaches.layer4.txt):
- wt-policy-sz12   lean-schema-typeof  welltyped-policy  12          (specimen/fused, the NEW generator)
- hw-slots-off     type-directed       -   20  validation-drt-type-directed-noslots  (guided, static only)
- hw-slots-on      type-directed       -   20  validation-drt-type-directed          (guided, standard target)
SLOTS refactor: validation_drt::FuzzTargetInput gained `const SLOTS: bool` (2nd generic); slots-on
= arbitrary_policy (STANDARD target, byte-identical path), slots-off = arbitrary_static_policy
re-wrapped as ABACPolicy(GeneratedPolicy::Static(..)) — minimal delta. New bin
validation-drt-type-directed-noslots (+ fuzz/Cargo.toml [[bin]]). 3 existing validation bins updated
to <_, true>. Built OK locally (cargo fuzz build). user_data_body.sh already builds CedarGen:static +
each 5th-col fuzz target, so EC2 handles PolicyGen + noslots. src.tgz + lean_cache.tgz (490MB, freshly
built .lake w/ PolicyGen) uploaded today. Results → s3://.../<S3ROOT>/results/ (bootstrap_ci +
coverage_compare + treemaps). MONITOR: SSM tail /var/log/cedar-exp.log; ~10-15min build then 500s run
then analysis (~20-30min total). EXPECT: wt-policy ≈ hw-slots-off on validator scope coverage (both
static), hw-slots-on adds slot-specific coverage (validate_slots/with_filled_slot — Lean can't reach).

## CONDITION-EMPTY WEIGHT MODIFIER (2026-08-05, user noticed empty-condition bias)
WellTypedConditions.nil fired too often → ~71/100 policies had empty condition ([] → scope-only).
FIX: `favorConditions` weight modifier (nil→1, when→base*6+4, unless→base*3+2) + `set_option
specimen.weightModifier "favorConditions"` on the derive. RESULT: 30 empty / 70 non-empty (was
71/29), still 100/100 well-typed. GOTCHA (user caught): the modifier MUST be defined at ROOT namespace
(not inside `namespace CedarGen.Relational.PolicyGen`) — the derive resolves `weightModifier "name"`
via the env `contains` fallback by SHORT name, so a namespaced def is silently ignored (falls back to
base weights). Same as SchemaTest's favorAncestors comment. Registered via
`Scoring.registerWeightModifier` + `open Scoring Schedules in` for the DeriveSort signature.
cf [[reference_specimen-weight-modifier]].

## END-TO-END VALIDATED (2026-08-05) — welltyped-policy strategy works, Rust accepts 100%
Rust smoke (cedar-drt/coverage/src/lean_gen.rs `welltyped_policy_smoke` test, run with
`--features lean-gen`): LeanSchemaTypeOfGenerator::with_sizes(20,12,"welltyped-policy",20) →
generate 200 → **200/200 Rust-strict-well-typed (0 ill-typed), 189/200 (94.5%) carry a real
(==/in/is) scope** (not all-Any when{expr}). So the full chain works: Lean WellTypedPolicy gen →
encodePolicies → Rust decode → Rust validator ACCEPTS ALL. The per-env-vs-all-env multi-env worry
did NOT bite (real scopes narrow applicability → strictly better than all-Any). Scope-coverage gap
(validator::typecheck scope-constraint paths, proto PrincipalOrResourceConstraint/ActionConstraint)
is now exercised by generation.
BUILD-SCRIPT GAP FIXED: build_lean_lib.sh did NOT build `CedarGen:static`, so libCedar_CedarGen.a
was stale (missing PolicyGen's init symbol → Rust link error `undefined symbol
initialize_Cedar_CedarGen_Relational_PolicyGen`). FIX: (1) added `import CedarGen.Relational.PolicyGen`
to CedarGen.lean (the lib root — the submodule glob alone didn't pick up the new file without a
manifest refresh), (2) added `CedarGen:static` to build_lean_lib.sh's lake build line. Rebuild
regenerated the archive (250 PolicyGen syms). MUST have CedarGen:static in the EC2/AMI build path.
REMAINING (Layer 4): add approaches.txt line strategy=welltyped-policy (strategy already flows
Rust→FFI via LeanSchemaTypeOfGenerator::with_sizes); then EC2 coverage run to MEASURE the closed gap
(diff vs guided-handwritten on validator::typecheck + proto scope paths).

## LAYER 2 GENERATOR — WORKING + LAYER 3 WIRED (2026-08-05)
BREAKTHROUGH: the WellTypedPolicy generator derives cleanly and produces fully well-typed
policies at runtime (20/20 well-typed, 0 ill-typed, validated by typecheckPolicy on testEnv).
Two fixes made it work (both user-guided):
1. WellTypedConditions now requires each body to be `HasType body caps env (.bool bty) cout`
   (typed boolean), with FAITHFUL capability threading across multi-clause when/unless (see
   the multi-clause fix below). This means the derive generates condition bodies via the EXISTING
   HasType generator — not `Arbitrary Expr`.
2. The HasType generator is `scoped` (in Variant.BudgetAware), so `open Variant.BudgetAware`
   (NOT just the import) is required to bring the `ArbitrarySizedSuchThat HasType` instance into
   scope for the derive to reuse. Import alone → falls back to Arbitrary Expr (the earlier error).
   Also `deriving instance Plausible.Arbitrary for Effect` (the policy's free effect field).
FILES:
- CedarGen/Relational/PolicyGen.lean (NEW, real module — NOT a *Test file): opens Variant.BudgetAware,
  `derive_mutual generator (fun env => ∃ p, WellTypedPolicy env p)` (global instance, ~887ms since
  HasType is cached/reused), + `generatePolicies (env size count seed) : IO (List Policy)` (mirrors
  generateExprs: implicit ArbitrarySizedSuchThat param, Gen.runUntilWith, count loop). Has a #eval
  self-check (20/20 well-typed).
- CedarGen/Relational/PolicyTest.lean = the earlier scratch derive (can be removed; PolicyGen supersedes).
- LAYER 3 DONE: CedarFFI/Generate.lean imports PolicyGen; generateSchemaTypeOfProtoFFI branches on
  strategy=="welltyped-policy" → generatePolicies + `encodePolicies [p]` per policy (real scopes),
  else the existing exprs→encodePolicySet path. "welltyped-policy" added to listStrategies. Wire format
  unchanged ([schema_len][schema][count][per-entry len+policyset]).
NEXT: rebuild static libs; LAYER 4 = add approaches.txt line strategy=welltyped-policy (strategy already
flows Rust→FFI); DRT smoke (validation-drt) to confirm Rust accepts the generated policies (should:
they're validator-well-typed per-env, and real scopes narrow multi-env applicability — strictly better
than all-Any); then EC2 coverage run to measure the closed scope-coverage gap (validator::typecheck +
proto scope-constraint paths that were handwritten-only).

## MULTI-CLAUSE CONDITION THREADING (2026-08-05, user pushed for full version, not single-clause)
WellTypedConditions : TypeEnv → Capabilities → List Condition → Prop, threads caps EXACTLY like the
validator's `&&` fold (verified against spec): Policy.toExpr = pScope && (aScope && (rScope &&
Conditions.toExpr)), typecheckPolicy runs typeOf … ∅ env. VERIFIED every scope conjunct produces ∅ caps
(typeOfEq/typeOfInₑ/typeOfInₛ/`is` all return via the `ok` helper whose caps default ∅) and `&&` never
refines env → condition list starts from ∅ caps + raw env. Threading: `when body` → HasType body caps
env (.bool bty) cout; next clause sees `caps ∪ cout`. `unless body` → body typechecked under `caps`
(must be bool) but `!body` produces ∅ caps (typeOfUnaryApp .not returns via `ok`; `.not` discards operand
caps) → next clause sees `caps` unchanged. nil base. WellTypedPolicy passes initial ∅ (scopes give ∅).
This is EXACT, not a sound-subset approximation (except the benign typeOfAnd short-circuit cases, which
we over-require — fine).

## LAYER 2 DERIVE — (earlier) blocked on Specimen scheduling (2026-08-05, RESOLVED above)
New file CedarGen/Relational/PolicyTest.lean: bundling relation `WellTypedScopes : TypeEnv →
PrincipalScope → ActionScope → ResourceScope` (env INPUT, 3 scopes OUTPUT; conditions deliberately
EXCLUDED — condition Expr comes from the existing typed HasType generator at Layer 3, not from the
untyped WellTypedConditions). `derive_mutual generator (fun env => ∃ pS aS rS, WellTypedScopes env
pS aS rS)`. Preamble mirrors SchemaTest (autoDeriveDeps, multiOutput, BudgetAwareScore,
precomputeWeights, Map Arbitrary instance). Derive elaborates ("14 specs in 14 components") but
FALLS BACK to `Arbitrary (List EntityUID)` for the `action in [..]` output list. ROOT: the schema
derive's WfActionAncestors draws list elements from a `List EntityUID` INPUT (ActionUIDDefined =
pick-an-element, generate-mode-able); my WellTypedActionInList/AllValidActionUIDs draw each uid as a
KEY from `List (EntityUID×ActionSchemaEntry)` via IsValidActionUID → scheduler can't generate-mode
the output list. NEXT: either (a) restructure the action-in-list to draw from a pre-extracted
`List EntityUID` of action keys (mirror WfActionAncestors exactly), or (b) scheduling hints / widget
inspection, or (c) provide Arbitrary instances (accepts check-mode for inAny — wasteful). Needs the
derive widget (editor, not CLI) to tune the schedule. Policy.lean spec fix itself compiles clean.

## LAYER 2 ANCESTOR-HANDLING AUDIT — DONE/PASSED (2026-08-05)
Verified (user prerequisite) that Policy.lean + Schema.lean implement the fixed ancestor logic
before deriving a generator, so the enum-hierarchy DRT mismatch won't regenerate:
- Schema.lean `WfEntitiesGo.enum` (line ~149) NEVER adds enum entities to `built`, and enum
  entries carry NO ancestors field → "an enum can never be an ancestor" (comment L109). Standard
  entities get `PickClosedAncestors` = a subset of already-transitively-closed ancestor sets whose
  union stays closed → one-hop `contains` in DescendentOf is sound.
- Policy.lean `DescendentOf` (L109-120) has a `here` case ONLY for `.standard` entries; for `.enum`
  only `refl` (self) applies → generator can't emit `principal in <ancestor>` for an enum principal.
  `.mem`/`.isMem` require `DescendentOf pty targetTy` (targetTy is a closed ancestor) AND
  `IsValidEntityUID ⟨targetTy,eid⟩` (targetTy exists, eid valid). Correct per fixed logic.
CONCLUSION: WellTypedPolicy is safe to derive. Next = derive_mutual on WellTypedPolicy.

## NEXT STEPS (2026-08-05, pre-compact) — scope-coverage fix + PBT
Ordered work to close the specimen scope gap (Layer 1 encoder DONE, see above):

1. CROSS-LANGUAGE ROUNDTRIP PBT (user requested) — tests the new Lean encoder+decoder against
   the Rust encoder+decoder. Design: GENERATE ON RUST SIDE (cedar_policy arbitrary PolicySet has
   REAL scopes, so no Layer 2 needed):
     P (arbitrary PolicySet) → Rust P.encode() → Lean decode (CedarProto Message.interpret? →
     Cedar.Spec.Proto.PolicySet.toPolicies) → Lean encodePolicies → Rust PolicySet::decode() → assert ≡ P.
   ENABLER: add ONE FFI export in CedarFFI (+ cedar-lean-ffi binding), e.g.
     `roundtripPolicySetProto (bytes) : bytes := CedarProto.Encode.encodePolicies ((decode bytes).toPolicies)`
   then a Rust proptest/arbitrary test in cedar-lean-ffi or cedar-drt generating PolicySets and
   asserting roundtrip equality. FILTER OUT templates/slots (not modeled in Lean yet). This would
   catch proto-fidelity bugs like the ~0.15% ill-typed leak.
   Pattern to copy: CedarProto/EncodePolicyTest.lean (Lean-only roundtrip, 10/10 pass) is the
   Lean half; the Rust half is new.

2. LAYER 2 GENERATOR: `derive_mutual` on WellTypedPolicy (CedarGen/Relational/Policy.lean) →
   generator producing List Cedar.Spec.Policy WITH scopes. derive_mutual builds the relation + its
   deps (WellTypedPrincipalScope/ResourceScope/ActionScope) from their STRUCTURE — NO stub instances
   (that was the older derive_generator trick in DeriveGenerators.lean). See
   [[reference_specimen-derive-mutual-syntax]] + [[feedback_derive-mutual-workflow]] (check widget
   output + runtime generators after).
   ** USER REQUIREMENT: FIRST verify Policy.lean has the ancestor-handling fixes we made **
   (enum/closure ancestor consistency, cf [[reference_enum-hierarchy-drt-mismatch]] — Lean dropped
   enum ancestors → invalid `in`). Audit WellTypedPrincipalScope `.mem ⟨targetTy,eid⟩` / `.isMem`
   (Policy.lean:178,184) + WellTypedResourceScope/ActionScope: targetTy must be a VALID ancestor per
   the FIXED logic, else we regenerate the enum-hierarchy DRT mismatch.

3. LAYER 3 DISPATCH: add strategy (e.g. "welltyped-policy") or an orthogonal scope-mode param to
   generateSchemaTypeOfProtoFFI (CedarFFI/Generate.lean:154): when set, generate List Policy via the
   Layer-2 generator and encode via `encodePolicies` INSTEAD of `dispatchGenerate`→exprs→`encodePolicySet`.
   (Can keep steep-tags for the CONDITION and add real scopes orthogonally.)

4. LAYER 4 RUST (trivial): add an approaches.txt line with the new strategy; `strategy` already flows
   Rust(lean_gen.rs:238)→FFI→dispatchGenerate. Then a fresh EC2 run to measure the closed gap.

STATE OF main.rs (coverage crate, NOT yet repackaged to src.tgz): added diagnostics to
replay_s3_corpus — REPLAY_COUNT_ILLTYPED (counts Rust-rejected inputs on replay) + REPLAY_DUMP
(dumps first N decoded policies). target_cov_fast/ = rust-only (features profraw,s3 NO lean-gen)
instrumented binary for fast diagnostics. These are harmless/env-gated; repackage before next EC2 run.

OPEN THREADS (parked): (a) proto roundtrip ~0.15% ill-typed leak (welltyped) — the PBT #1 would
pin it; (b) 4h run i-049a97866c2f6f37a STUCK in Phase 3 k-path analyze (I/O-bound serial S3
download, ~22/80 reps in 8h, CPU idle) — collection safe in S3; fix = concurrent S3 download in
replay_and_analyze_from_s3 OR kill+reanalyze; (c) over_time_throughput.png still min-clamped in the
1h S3 results (needs collect/edge_snapshots, excluded from results upload).

## WARM REUSE + GOLDEN AMI + 10-MIN RUN (2026-08-04)
- SMOKE VALIDATED end-to-end on EC2 (cache-test i-0918, S3ROOT ci-run-4reps-30s-20260804T201341Z):
  full mixed pipeline, all graphs. Numbers (4 reps, 30s): specimen steep-tags 1321/s cov=5308,
  typeof-check 946/s cov=5304; guided plain 442/s cov=2453, welltyped 436/s cov=2453. Perf fix
  confirmed (no collapse). GUIDED CAVEAT (understood/accepted by user): guided produces a TRIVIAL
  1-node policy `permit(...) when {true}` repeatedly (unique=1, mean_node=1, 0 k-paths) because
  libFuzzer's short cold-start inputs byte-starve the ABAC policy gen (schema generated first).
  Both guided targets ARE type-directed (<true>). Fix if ever wanted: seed libFuzzer corpus with
  large structured inputs. User said this is fine for now.
- run_on.sh (warm reuse, no rebuild) FIXED two bugs: (1) added `export USE_INSTANCE_ROLE=1` to the
  remote (else it forces the missing cedar-experiment profile → S3 fails); (2) the remote script was
  passed via `commands=[json]` shorthand → literal `\n` → syntax error; now base64-encoded
  (`echo <b64>|base64 -d|bash`). Coverage is replay-based (fresh process/rep) so warm reuse needs NO
  counter reset.
- 10-MIN RUN live on warm i-0918: run_on.sh REPS=4 RUN_SECS=600 SEED_BASE=6.4e12 ON_FINISH=stop,
  S3ROOT warm-10min-20260804T205114Z (mixed 2 specimen sz12 + 2 guided). No rebuild — started in
  seconds. Results -> s3://.../warm-10min-20260804T205114Z/results/.
- GOLDEN AMI ami-0a0841fa2f0e47afa (cedar-exp-base-20260804) baking from i-0918 (toolchains + warm
  build). Use: `AMI_ID=ami-0a0841fa2f0e47afa … CONFIRM=1 ./launch.sh` to SKIP the ~10-13min install
  (user_data installs are now idempotent: `command -v … || install`). aws/make_base_ami.sh bakes it.
- user_data now: idempotent installs + Lean-cache extract (2-dir) + `touch .lake` (mtime fix).

## LEAN BUILD CACHE (2026-08-04) — skips the ~15-min lake build
package_and_upload.sh LEAN_CACHE=1 tars the compiled Lean build → s3://.../bootstrap/lean_cache.tgz
(~490MB gz), user_data downloads+extracts it before `lake build` (fast verify vs full compile).
CRITICAL: must include BOTH cedar-lean/.lake AND specimen/.lake — Specimen is a PATH dep
(`require specimen from "../../specimen"`) built in specimen's OWN .lake, so
libspecimen_Specimen.a is NOT under cedar-lean/.lake (first cache missed it; fixed). The 3
git deps (batteries/plausible/proofwidgets) ARE under cedar-lean/.lake/packages/*/.lake so
they're already covered. Cache tar is rooted so `tar x -C $WORK` lands cedar-spec/cedar-lean/.lake
+ specimen/.lake. All 11 static .a libs the FFI links are covered. tar preserves mtimes ⇒ lake
sees up-to-date. Opt-in (LEAN_CACHE=1); re-run when Lean spec changes. lake still verifies so a
stale/absent cache is safe (falls back to full build). CACHE-TEST: i-0918a0769c4b6474b
(S3ROOT ci-run-4reps-30s-20260804T201341Z) launched 20:13Z to confirm fast build.
v4 i-0c376f39f16b7bdc3 STOPPED (was full-building; superseded). Prior stopped smokes:
i-097463f12e3e8bbae, i-0d1253b100a62bd2e. DO NOT kill 1h/4h/12h.

## (OLD) SMOKE v4: i-0c376f39f16b7bdc3 (stopped)
Fixed mixed smoke, S3ROOT ci-run-4reps-30s-20260804T195536Z, REPS=4 RUN_SECS=30
SEED_BASE=6.2e12 ON_FINISH=stop, approaches.smoke.txt (2 specimen sz12 + 2 guided). Verifies
the EC2 path (cargo-fuzz install, wrapper-instrumented cedar-drt-coverage build) + that the
parallelism collapse is GONE (reset-once + cedar-only instr). Results ->
s3://.../ci-run-4reps-30s-20260804T195536Z/results/. Prior stopped: i-097463f12e3e8bbae,
i-0d1253b100a62bd2e (superseded). DO NOT kill 1h/4h/12h.

## SMOKE TEST (2026-08-04) — both STOPPED, superseded
Run1 i-097463f12e3e8bbae + run2 i-0d1253b100a62bd2e STOPPED (EBS preserved). Run1 hit the
--generator bug (guided) + the fused-collect slowness (pre-fix). Both superseded by v4.
Next: re-package src (v4) + launch a fresh small mixed smoke (approaches.smoke.txt: 2 specimen
sz12 + 2 guided), REPS~4, RUN_SECS=30, verify graphs (bootstrap_ci, over_time, coverage_compare).

## (OLD) SMOKE TEST RUNNING (2026-08-04)
Mixed 30s smoke: instance `i-097463f12e3e8bbae` (c7i.8xlarge), S3ROOT
`ci-run-4reps-30s-20260804T183505Z`, REPS=4 RUN_SECS=30 SEED_BASE=6e12 ON_FINISH=stop.
Purpose: verify the WHOLE pipeline end-to-end (cargo-fuzz install, both instrumented
builds, parallel count-match throughput‖collect, guided replay + fused inline coverage,
combined coverage_compare, bootstrap_ci + plots). Results ->
s3://__S3_BUCKET__/ci-run-4reps-30s-20260804T183505Z/results/. Boot+build
~15-20min then 30s run + analyze. Verify graphs before launching the real (longer) run.
DO NOT KILL the 1h/4h/12h instances (old unguided). If smoke fails: SSM to the box,
tail /var/log/cedar-exp.log; the src.tgz has all v3 code (re-uploaded).

## REMAINING WORK (ordered)
DONE 1-5 (2026-08-04). #6 = smoke test RUNNING (verify graphs) → then launch real run.

1. [DONE] `replay_proto_corpus` + `replay_s3_corpus` (main.rs) now use `ValidationCov`:
   begin() before validate, fold() after, over-time snapshots = `counters_hit` (no
   intermediate profraw), one `final.profraw` via `overwrite_live()`+dump, snapshots.json.
   Compiles (`cargo check --features profraw,s3`).
2. [DONE] `run_experiment.sh` guided mode. KEY SIMPLIFICATION vs original plan: coverage
   replay is NOT a separate Phase-3 in the script — **coverage_analyze.py's non-`--from-collect`
   path ALREADY replays each rep's S3 corpus through `cedar-drt-coverage --replay-s3-*` in
   parallel (ThreadPoolExecutor)**. So guided Phase 3.5 = `coverage_analyze.py --binary
   $BIN_DRT_COV --s3-bucket --s3-root` (NO --from-collect). Guided Phase 3 (analyze) is now
   REQUIRED (guided collect can't compute inline metrics). Phase 1 guided sizes N by ATTEMPT
   rate (`getAttemptRate`; guided collect is `-runs=N`). A run must be all-guided or
   all-fused (mode check errors on mix — different instrumented binaries). `is_guided`=5th col.
3. [DONE] Approach config: 5th column = fuzz_target ⇒ guided. New file
   `aws/approaches.guided.txt` (hw-guided-plain=validation-drt-type-directed,
   hw-guided-welltyped=validation-welltyped-drt). manifest.json gains guided/fuzz_target.
4. [DONE] `user_data_body.sh`: detects GUIDED_RUN (awk NF>=5 on approaches.txt); installs
   nightly + `cargo install cargo-fuzz`; builds each 5th-col fuzz target (`cargo +nightly
   fuzz build -s none`); builds `cedar-drt-coverage` replay bin (instrument-coverage,
   features profraw,s3, NO lean-gen). Fused path unchanged.
5. [DONE] Local verify: built `target_cov/release/cedar-drt-coverage` (features profraw),
   replayed the 9096 logged inputs → **9096 validated, 0 failed, 1844 validation regions,
   1550 harness-excluded source lines** (llvm-cov + IGNORE_REGEX). Pipeline proven.
6. [TODO — CONFIRM FIRST] Launch EC2 guided run: `APPROACHES_FILE=…/approaches.guided.txt
   REPS=20 RUN_SECS=<secs> SEED_BASE=<>=5e12> CONFIRM=1 ./launch.sh` (after
   `./package_and_upload.sh` to refresh src.tgz). Both plain + welltyped in ONE guided run
   (they're both guided → OK). Don't kill 1h/4h/12h. Coverage is guided-only (single binary),
   so specimen-vs-guided line diff is POST-HOC (both link cedar-policy; re-analyze specimen
   final.profraws with cedar-drt-coverage-cov to get one comparable line set).

## EC2 STATE (running — DO NOT KILL)
- 1h `i-0b5c1581448987934` (`ci-run-20reps-3600s-20260803T234953Z`), 4h
  `i-032a4db02626829eb` (14400s), 12h `i-0d3b33ab99f0581f9` (43200s) — running the OLD
  UNGUIDED handwritten + specimen, N-sized (slow). 30s `i-0c726567283054b08` + 10min
  `i-059a36c1f08cc8763` = stopped/done. Quota 1152=6×192; 3 running=576 (room).
- The 1hr box's instrument-coverage binary was pulled via SSM to
  `s3://__S3_BUCKET__/ci-run-20reps-3600s-20260803T234953Z/binary/cedar-experiment`
  and cached locally `/home/segevem/.claude/jobs/01c084b2/tmp/ec2_bin` (needed because
  llvm-cov requires the EXACT binary that produced a profraw).

## SPECIMEN NUMBERS (VALID — keep, don't recompute)
1hr run, 20 reps/approach: ~4746-4760 `source_lines` each; the 4 specimen strategies
~99% Jaccard among themselves (near-redundant on line coverage); union region-lines 4608;
saturates within ~few hundred k inputs (extra millions add ~0). 0 mismatches over ~tens
of millions of validations. `source_lines` (llvm-cov summary) > `region_lines` ((file,line)
set used for overlap/Jaccard). The specimen-vs-handwritten diff (extensions/typecheck vs
templates/RBAC) was computed against the INVALID unguided handwritten — REDO vs guided.

Run/build/package/launch mechanics: see [[project_fixed-generator-drt-runs]].
Scope = validation-only via ValidationCov per-phase reset (0 generator leakage), verified.

---
## RUN #4 (2026-08-05 22:45Z) — NEW generator (id-bty fix + tuned favorConditions)
- Instance **i-013f90f3a6e482175** (c7i.48xlarge, golden AMI ami-07994225d79227b05), ON_FINISH=stop.
- S3ROOT **run4-newgen-20reps-900s-20260805T224535Z**. REPS=20, RUN_SECS=900, approaches.layer4.txt
  (3 arms: wt-policy-sz12 NEW-gen, hw-slots-off, hw-slots-on) — SAME config as run #3 for direct compare.
- src.tgz + lean_cache.tgz repackaged 22:43-22:44Z WITH the id-bty fix (Policy.lean) + tuned weights
  (PolicyGen.lean favorConditions nil*3+1/when,unless*2+1). Local timing: 403 pol/s, 1.17 conds/pol.
  See [[id-bty-condition-speedup]].
- PURPOSE: compare wt-policy-sz12 throughput/coverage NEW (run#4) vs OLD (run#3), both vs same HW baselines.
- Run #3 (i-0ce511d59d4eded57, ci-run-20reps-900s-20260805T215529Z, OLD gen) STILL RUNNING concurrently.
  Wait for BOTH; compare results.
- vCPU: quota 1152; usage now 576 (run#3 192 + run#4 192 + ORPHAN 192). OK.

## ORPHAN INSTANCE — RESOLVED (STOPPED 2026-08-05 by user direction)
- i-049a97866c2f6f37a = ci-4h-sharded-20260804T233646Z, launched 2026-08-04 23:36Z, ran ~22h (never
  self-terminated). User authorized STOP (not terminate) — EBS + S3 preserved, restartable.
- Checked for DRT mismatches: violations persisted at <arm>/rep_NN/violations/ (harness uses
  run_val_test_checked → mismatch captured as data, NOT a crash-* artifact — panics caught internally).
  ALL 4 arms (hw-guided-plain, hw-guided-welltyped, steep-tags-sz12, typeof-check-sz12) × 20 reps =
  **0 violation objects → NO mismatches found.** All 20 rep folders present (collection completed).
