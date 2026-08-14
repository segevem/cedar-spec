---
name: guided-drain-loss-and-mapping
description: "Root cause + fix for the recurring 'guided coverage corpus smaller than throughput count / over-time curve stops before the run end' problem: lossy tmpfs drain + wrong wall-clock mapping (probe vs collect)"
metadata: 
  node_type: memory
  type: reference
  modified: 2026-08-14T10:48:48.795Z
  originSessionId: 80b33588-72ac-4fb9-a607-0ff17df90158
---

# Guided corpus < throughput count, and the over-time curve ends early

The recurring "we fixed this 1000 times" bug. Two independent causes; BOTH must be fixed.

## Setup (why there's a mismatch at all)
For a GUIDED arm the pipeline runs TWO separate cargo-fuzz processes (run_experiment.sh):
- **throughput probe** (`run_guided_throughput`): NO `CEDAR_FUZZ_LOG_DIR` → generates without logging/draining
  (fast). Writes `throughput/_fuzz_stats_rep_NN.json`; `throughput/rep_NN.json` is derived from it. This is
  the PURE generation rate (e.g. 947k–1.66M valids/hr, varies per rep).
- **collect** (`run_guided_collection_with_drain`): sets `CEDAR_FUZZ_LOG_DIR` (a `/dev/shm` tmpfs) so the
  target logs each valid input's proto `[schema_len‖schema‖policies]` (`encode_replayable`), and a drain
  thread moves files → `on_file` (batched S3 upload) → deletes. Writes its OWN timeline to
  **`collect/_fuzz_stats_rep_NN.json`**. The corpus (rep_NN/corpus/batch_*.bin) is what the drain saved.

The stored corpus format is CORRECT protobuf (not raw bytes, not re-encoded). op_hist/analyze read it fine.

## Cause 1 — LOSSY DRAIN (corpus << count)
`guided_log::log_input` was best-effort: `if fs::write(tmp).is_ok()`. When the fuzzer out-runs the S3 drain,
tmpfs fills, the write FAILS, and the input is SILENTLY DROPPED (but `VALID` was already bumped → the stats
overcount). Retention swings **6–100% per rep** with I/O contention (40+ procs on a c7i.48xlarge). E.g. a
validation-boost hw rep kept 60k of 946k = 6%.
FIX (cedar-drt/fuzz/src/lib.rs `guided_log::log_input`): BACKPRESSURE — every 256 inputs, if the pending
file count in the log dir exceeds `CEDAR_FUZZ_DRAIN_HIGH` (8000), BLOCK until it drops under
`CEDAR_FUZZ_DRAIN_LOW` (2000); and RETRY the write instead of dropping. Throttles generation to the drain
rate → tmpfs bounded → nothing dropped → `collect VALID == corpus size`. (Throughput then reflects the true
generate+store rate, which is the honest number.)

## Cause 2 — WRONG WALL-CLOCK MAPPING (curve ends before run end)
The source-coverage / diversity over-time x-axis maps `corpus_idx` → time via a valid_count→time timeline.
It was using the **throughput PROBE** (`throughput/rep_NN.json`), which generated FASTER (no drain) than the
collect that produced the corpus — so `corpus_idx_max` mapped to an early second (e.g. 762k mapped to 2831s
instead of 3600s), and the curve stopped short of the run end.
FIX (plot_over_time.py `time_map`, plot_over_time_excl.py `timemap`): prefer the COLLECT's own timeline
**`collect/_fuzz_stats_rep_NN.json`** (snapshots = `(elapsed_ms, valid, total)`; use valid→ms/1000) when it
exists (guided); fall back to `throughput/rep_NN.json` for fused/specimen arms (which count-match the probe
and have no collect stats). Only fully correct once Cause 1 is fixed (else collect VALID still overcounts vs
the dropped corpus). Also added a dashed forward-fill of the saturated plateau to the longest arm's end as a
display nicety.

## ⚠️ CORRECTION (2026-08-12): the MAIN guided drop is the S3 UPLOADER, not tmpfs
The `log_input` backpressure fixed the tmpfs-write-fail drop and made the FUSED arms count-match
20/20 (ratio 1.00). But the GUIDED arms still undershoot badly (hw-slots-off 8/20 count-matched;
rep05 corpus=98k while the collect GENERATED 1.56M valids over 3701s = ran the FULL hour, matched
the probe's 1.56M — NO crash, NO bug found, NO early exit). Root cause = **`experiment/s3.rs:132`
`StreamingUploader`: `let _ = client.put_object()...send().await;` IGNORES the S3 result (no retry)
and `uploaded += 1` counts it regardless.** Under ~20 concurrent reps, S3 request-rate throttling
(503 SlowDown) fails many put_objects → SILENTLY DROPPED. The drain (guided.rs) deletes each local
file right after QUEUING it to the uploader (not after confirmed upload), and count-match counts
files READ not files durably-in-S3 → it "completes" while the S3 corpus is short.
Do NOT attribute the guided undershoot to a found bug / libFuzzer crash-halt / tmpfs drops.
FIX: retry `put_object` with exponential backoff (esp. 503) in StreamingUploader, count `uploaded`
only on success, hard-fail on exhausted retries. Collect stats live at
`<arm>/collect/_fuzz_stats_rep_NN.json` (valid_count/elapsed_ms) — compare to corpus_idx_max to see
generate-vs-drain loss per rep.

## ⚠️⚠️ SECOND CORRECTION (2026-08-13): for the -v2 boost runs the guided over-time curve ending
## early is NOT collect/upload loss — it's PHASE 3.5 REPLAY-SHARD death (S3-stream under concurrency)
Verified on `ci-boost-lossless-symcc-20reps-3600s-v2` hw-symcc-plain: the COLLECT collected the full
count (phase2 log: rep05 "done. 1,583,042 collected" = matched target) AND the S3 corpus is COMPLETE
(rep05 = 1584 batch files × 1000 = ~1.58M, uploads protected — the bounded-channel/backpressure worked).
What's short is `covIdxMax` in `coverage/rep_NN_over_time.json` (rep05=98,993 ≈ EXACTLY 1 of 16 shards;
rep17=714,507 ≈ 11/16) — integer multiples of shard size ⇒ contiguous replay shards DIED.
PROOF it's NOT corpus content / hang / backtrack / OOM: `symcc_repro corpus <local rep05 corpus>`
(download-then-replay, 1 process) replayed ALL 1584 files = 2,837,617 checks, 0 mismatches, 0
compile-fails, exit 0, ~1.4GB peak. So the inputs are clean; a per-input timeout would fix nothing.
ROOT CAUSE = the SHARDED replay infra: `coverage_analyze.py replay_one_shard` STREAMS each shard's batch
range straight from S3 (`stream_batches_sharded`) with 16 shards × 20 reps × 3 arms concurrent, each with
its own Lean runtime → S3 GET throttle / listing eventual-consistency (see the code's own comment at
coverage_analyze.py:334 "replay shards stream 0 inputs → coverage silently empty") kills shards. FUSED
arms replay their FULL corpus (3–4.7M inputs, 0 shard loss) because [same oracle] — so it's not volume;
guided just happened to lose shards. `assemble_rep` uses only the CONTIGUOUS PREFIX of surviving shards
for the over-time series, so one missing early shard truncates covIdxMax (final union coverage may be more).
FIX (matches "hw doesn't backtrack, no timeout needed"): make the replay read the corpus RELIABLY —
DOWNLOAD-then-replay locally per rep (proven to work by symcc_repro) instead of concurrent per-shard S3
streaming; or robust-retry the S3 stream + verify full key listing before slicing. Then re-run PHASE 3.5
for the guided arms only (corpus already in S3, no re-collect) → full covIdxMax → full-hour curves.
Graphs (2026-08-13, both runs) live in s3://.../graphs-20260813/ + .experiment_holding/graphs_20260813/;
plot_over_time.py was updated to grid-resample onto a common probe-time grid (NaN past each rep's last
sample) + line-not-dots for dense k-paths; plot_node_hist.py updated to linear + difference-highlights.

## ✅ FIXED (2026-08-13): regenerate guided coverage-over-time WITHOUT re-collect (corpus intact)
The guided over-time curve ending early (hw ~2500s) = PHASE 3.5 replay-shard death from S3-stream
CONCURRENCY (191 shard-tasks at once). Two-part fix, no re-collect (corpus already complete in S3):
1. THROTTLE: `coverage_analyze.py --replay-shards 16 --jobs 24` → far fewer concurrent S3 streams →
   ALL 16 shards survive → full covIdxMax for every rep (verified: symcc hw all 1.05–1.6M; val hw all
   0.88–1.6M). (`--replay-shards 1` is WRONG: it sets REPLAY_SNAPSHOTS=0 → 1 point; the non-sharded
   process_rep+snapshots path gives per-batch DELTA coverage 33–36, not cumulative — dead end. Keep
   16 shards for the cumulative over-time points, just lower --jobs.)
2. CORRECT COVERAGE_IGNORE_REGEX per target (else covered_lines=0): coverage_analyze reads it from env
   (line 42). For symcc EXPORT the symcc regex `.../cedar-policy-core|cedar-policy-validator` (+ TARGET=
   symcc-term-never-errors + INSTRUMENT_CRATES="cedar_policy_symcc cedar_drt_coverage"); for validation
   leave it UNSET (default = measures the validator, drops symcc) + TARGET=validation-drt. Also export
   COVERAGE_EXCLUDE_LINES=spec_unreachable_exclude.txt. Result: symcc hw coveredMax ~2374, val hw ~5811.
INSTRUMENTED BINARIES: symcc-instrumented cedar-drt-coverage is at target_cov/ (from -v2, INSTRUMENT_CRATES=
cedar_policy_symcc). For validation build a SEPARATE one: PATH=/root/.cargo/bin:/root/.elan/bin:/opt/exp/protoc/bin,
PROTOC=/opt/exp/protoc/bin/protoc, LEAN_LIB_DIR=$(lean --print-libdir), RUSTC_WRAPPER=experiment_scripts/
instrument_cedar_only.sh cargo build --release --bin cedar-drt-coverage --features "profraw,s3,lean-gen"
--target-dir target_valcov. (rustc/lean/protoc all need explicit PATH on the instance.)
PLOT: plot_over_time.py was rewritten to GRID-RESAMPLE reps onto a common probe-time grid (NaN past each
rep's last real sample) so ragged/undershooting reps don't truncate everyone to the shortest — curve spans
the full hour, CI widens where fewer reps reached. Dense metrics (k-paths/throughput) draw as a LINE (no
dot-markers); sparse coverage keeps markers. plot_over_time_excl.py similar. Fixed coverage PNGs (both runs,
full hour) in s3://.../graphs-20260813/ + .experiment_holding/graphs_20260813/.
k-path over-time (diversity_over_time in analyze/rep_NN.json): CHECKED — NOT truncated (guided has full
128 pts to full corpus; PHASE 3 analyze wasn't lossy). "Too few points" was just plot_over_time's default
--grid 40; re-plot k-paths/unique with --grid 128 (native diversity resolution = the real max; higher just
interpolates). Dense metrics draw as a LINE (no dot-markers).
TAIL-JUMP ARTIFACT (fixed): grid-resample extends to the GLOBAL max per-rep end-time (one rep maps slightly
past 3600 via its probe), so the last grid columns are backed by only 1-2 longest reps → median ticks
up/down (visible on near-saturated 2-path + the coverage sz20 end-dip). FIX in plot_over_time.py: mask grid
columns with support < ceil(n/2) reps (set med/lo/hi NaN) → curve ends cleanly ~3600.
PERSISTED guided coverage over_time (so re-plots don't need the instance): s3://.../graphs-20260813/covdata/
{symcc,val}/<guided>/coverage/rep_NN_over_time.json (the throttled non-lossy regen). Fused coverage over_time
is in each run's results/<arm>/coverage/. All final graphs (both runs, full hour, tail-masked) in
s3://.../graphs-20260813/ + .experiment_holding/graphs_20260813/.

## Validation
Requires a RE-RUN with the backpressure build (existing runs can't be re-plotted correct — their corpora are
already lossy). After re-run: `corpus_idx_max ≈ collect/_fuzz_stats valid_count`, and the over-time curve
spans the full RUN_SECS for every arm. Boost runs: S3ROOT `ci-run-boost-{symcc,validation}-20reps-3600s`.
See [[coverage-only-reuse-workflow]], [[generator-weight-tuning]] for run mechanics.
