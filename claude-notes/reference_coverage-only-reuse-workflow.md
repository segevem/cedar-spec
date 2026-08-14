---
name: coverage-only-reuse-workflow
description: "How to re-run coverage over an EXISTING corpus (no regen), apply the exclusion, and plot real-wall-clock over-time"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 60db3c98-5034-4030-861c-4468d8c04ec7
  modified: 2026-08-07T23:19:23.217Z
---

# Coverage-only over an existing corpus + real-wall-clock over-time plotting

## Reuse an existing corpus (skip generation) — REUSE_CORPUS_S3ROOT
I added a **`REUSE_CORPUS_S3ROOT`** mode to `run_experiment.sh` (gates PHASE 1+2 generate, PHASE 3
k-path, and the settle-wait; points `coverage_analyze.py --s3-root` at the reuse corpus). Rebuilds
byte-identical corpus otherwise = pointless, so ALWAYS reuse when only the coverage/analysis changed.
Launch (EC2), from `cedar-drt/coverage/experiment_scripts/aws/`:
```
./package_and_upload.sh   # bundles patched tooling + exclude files (LEAN_CACHE=1 only if Lean changed)
REUSE_CORPUS_S3ROOT=<old-run-S3ROOT> COV_FEATURES=profraw,s3 TARGET=rust-only \
  INSTANCE_TYPE=c7i.12xlarge ON_FINISH=stop APPROACHES_FILE=$PWD/approaches.validation-2size.txt \
  REPS=20 S3ROOT=ci-cov-<tag> CONFIRM=1 ./launch.sh
```
- `COV_FEATURES=profraw,s3` (NOT lean-gen) + `TARGET=rust-only` → coverage build needs NO Lean libs;
  rust-only `Validator::validate` is enough for VALIDATOR line coverage. Both are env-overridable now
  (I made COV_FEATURES overridable; launch.sh propagates REUSE_CORPUS_S3ROOT + COV_FEATURES).
- Exclusion is DEFAULT-ON: run_experiment.sh sets `COVERAGE_EXCLUDE_LINES=$COVERAGE_DIR/spec_unreachable_exclude.txt`
  if present (disable with empty). It emits `over_time_source_lines_excluded.png` (raw-vs-excluded overlay).
- **Do NOT run coverage-only locally for the full corpus**: local S3 streaming is ~5 MB/s → hours for
  ~100 GB. On EC2 (same-region) it's ~30–45 min. (~$1–2 on c7i.12xlarge, generation skipped.)
- coverage_analyze.py CLI (standalone): `--root --binary <cedar-drt-coverage> --manifest --reps
  --replay-shards --s3-bucket --s3-root`. Needs the s3+profraw INSTRUMENTED binary:
  `RUSTFLAGS="-C instrument-coverage" cargo build --release --bin cedar-drt-coverage --features "profraw s3"`.
  Replay dispatch is gated by `#[cfg(feature="profraw")]` (without it, --replay-* is silently ignored
  and it runs the default GENERATOR). corpus_idx ≈ generation valid_count (same corpus, same order).

## Real wall-clock over-time (do NOT approximate)
Throughput timing lives at **`<S3ROOT>/results/<approach>/throughput/`** (NOT top-level `throughput/`
— that's empty). specimen = `rep_NN.json` `{snapshots:[{valid_count,elapsed_secs}]}` (720 pts);
hw/guided = `_fuzz_stats_rep_NN.json` `{snapshots:[[time_ms,valid,total]]}`. Coverage over_time
(`results/<approach>/coverage/rep_NN_over_time.json`) has `corpus_idx,covered_lines,covered_lines_excl`.
Map x = `interp(corpus_idx, valid_count, elapsed_secs)` per rep. profdata itself is TRANSIENT (deleted
after llvm-cov; NOT in S3) — so to re-diff exact lines you must re-replay.

## Plotter: plot_over_time_excl.py (NEW, in experiment_scripts/, bundled)
- Overlay: dashed=all lines, solid=error+annotation-excluded, per arm, mean±95% over reps.
- Uses the real `timemap()` (both throughput formats). `--ymin/--ymax` for a zoomed view.
- Coverage MUST start at (0,0); plot ACTUAL shard-boundary samples as MARKERS + straight lines
  (segments between samples are interpolation, not data). Coverage is sampled at shard boundaries
  (~16 pts), shard size = corpus/n_shards, so big-corpus arms' first sample is later (bump
  `--replay-shards` for finer early sampling).

## S3 runs (bucket __S3_BUCKET__)
- `ci-run-20reps-3600s-20260807T041135Z` = the 3-arm 1hr corpus run (wt-policy-sz12, wt-policy-sz20,
  hw-slots-off). Has corpus + throughput + analyze(kpath) + rendered PNGs. THE reuse source.
- `ci-cov-excl-20260807T185731Z` = coverage-only reuse w/ error+annotation exclusion (its results/).
- Graphs saved durably in `cedar-drt/coverage/graphs_err_excl/` (realtime, zoom, venn).
See [[error-annotation-coverage-exclusion]] and [[specimen-vs-hw-coverage-findings]].
