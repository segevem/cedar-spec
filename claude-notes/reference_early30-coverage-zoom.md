---
name: early30-coverage-zoom
description: How to build the fine-grained first-30s source-line coverage curves (cov_early.py) + the specimen-saturates-instantly finding
metadata: 
  node_type: memory
  type: reference
  originSessionId: 80b33588-72ac-4fb9-a607-0ff17df90158
  modified: 2026-08-14T16:57:42.189Z
---

# First-30s coverage zoom (cov_early.py)

The main over-time graph samples coverage at replay SHARD boundaries → 16 points over the whole
hour → the FIRST sample sits at ~1/16 of the corpus (~99k inputs ≈ 140s), so the opening seconds
are invisible. `cov_early.py` (deployed to instances at `/opt/exp/early/`, source in
cedar-drt/coverage/experiment_scripts/) fills that in.

## Method (per arm, per rep)
1. Read the throughput timeline → valid_count↔elapsed_sec. TWO schemas: guided arms have
   `results/<arm>/throughput/_fuzz_stats_rep_NN.json` (snapshots=[elapsed_ms,valid,total]); fused
   specimen arms have `results/<arm>/throughput/rep_NN.json` (snapshots=[{valid_count,elapsed_secs}]).
   `fetch_timeline` tries both.
2. Map window+2s → n_window inputs; download just the first ceil(n_window/1000)+1 corpus batches
   from S3 (`<arm>/rep_NN/corpus/batch_*.bin`, 1000 entries each, `[u32-le len‖payload]` frames).
3. Re-split into fine chunk files (two-tier: STEP_FINE=50 for the first FINE_N inputs to catch the
   initial rise, STEP_COARSE after). Replay EACH chunk alone through the instrumented binary
   (`--replay-proto <chunkdir>`, REPLAY_SNAPSHOTS=0 → dumps that chunk's final.profraw), then
   CUMULATIVELY merge chunk profraws and read `covered_counts` (raw, excl source-lines) at each
   boundary — mirrors coverage_analyze.assemble_rep. Import coverage_analyze so IGNORE_REGEX/EXCLUDE
   match the baseline exactly. Map corpus_idx→time via the timeline; keep t≤window.
4. `plot_early30.py` (reads <root>/<arm>/rep_NN_early.json): prepend (0,0), grid-resample onto a
   common time grid (NaN past each rep's last sample), median + 95% bootstrap CI, tail-mask columns
   with support < ceil(n/2). Overlays arms; colors follow the manifest order (sz12,sz20,hw =
   blue,red,green) to match the main graphs. Emits linear + symlog-x (linthresh=0.5) companion.

## GOTCHAS
- Metric MUST be profdata source-lines (covered_counts), NOT `count_hit()`/`counters_hit`. count_hit
  counts covered LLVM *counters* — for the symcc binary it saturates at ~116, a totally different
  scale from the ~2374 source-lines the main graph uses. (The fused-collect over_time uses
  counters_hit too, but only because for THAT binary it happens to ~track; don't rely on it.)
- Use `--target rust-only` for VALIDATION coverage: it drives the identical `Validator::validate`
  (validator coverage is the same as validation-drt; Lean isn't instrumented) but skips the Lean
  runtime, which HANGS the proto replay (validation-drt replay ran >15min on 1000 inputs). symcc uses
  `--target symcc-term-never-errors` (drives the instrumented symcc compiler).
- Val binary export is SLOW (~8-12s each; core+validator crate = huge llvm-cov JSON). With 250-step
  chunks that's ~200 exports/rep → ~30min/arm. Coarsen: STEP_FINE=50 FINE_N=1000 STEP_COARSE=1000
  (~40-70 chunks/rep) — the plateau needs no fine sampling. symcc export is ~0.25s (small crate).
- Canonical instrumented binaries live on the boost instances at
  coverage/target_cov/release/cedar-drt-coverage (symcc instance: symcc-instrumented cedar_policy_symcc;
  val instance: cedar-only = core+validator, built Aug12 for the run; `target`=plain build WITHOUT
  the profraw feature → `--replay-proto` is ignored and it enters an endless GENERATION loop, don't use).
- Per-process replay init is ~0.1s (cheap) → the N-small-processes-per-chunk approach needs NO
  binary rebuild.
- SSM: base64-encode scripts (`echo <b64>|base64 -d|bash`) to avoid newline/quoting mangling; the
  local Bash tool caps at 2min unless you pass timeout — long polls get killed, poll async instead.

## FINDING — specimen saturates coverage almost instantly; handwritten crawls
Fair excluded/source-line coverage, median over 20 reps, first 30s (boost runs):
- SymCC (raw==excl): specimen sz12 1555→2369, sz20 1803→2391 (both reach ~2370-2390 by ~5s, most of
  it within the FIRST ~50 inputs / <0.3s); handwritten 348→403. Full-run union ≈2374.
- Validation (excl): specimen sz12 3989→4781, sz20 4212→4769 (≈82% of the ~5811 full-run union within
  30s, bulk in the first ~50 inputs); handwritten 2088→2123 (~37%).
So specimen reaches near-plateau coverage in <1s while the handwritten fuzzer is still far below it at
30s. Deliverables: s3://__S3_BUCKET__/graphs-20260813/early30/early30_{symcc,val}[_logx].png
+ .experiment_holding/early30/. See [[specimen-vs-hw-coverage-findings]], [[guided-drain-loss-and-mapping]].

## Overlaying the early dots ON the full-hour graphs (overlaid_early/)
plot_over_time.py (symcc covered) and plot_over_time_excl.py (val excluded) gained `--early <dir>`
(cov_early.py output), `--early-window`, `--xscale symlog`. Per arm we plot exactly TWO measured dots
(`early_two_points`: the first measured sample + the value at t=window) and draw a connector line
[dot1 → dot2 → main curve's first real sample] so the curve is CONTINUOUS from the opening seconds
through the full run.
FINAL DESIGN = TWO SEPARATE PICTURES (user: "the zoom in box should be just a separate picture" —
after briefly trying it as an inset). Deliver per run:
 (A) the PLAIN overlaid full-hour graph, UNCHANGED (the existing graphs_20260813/overlaid/*_overlaid.png,
     linear, markers, legend, origin) — no early drawing on it at all.
 (B) a SEPARATE standalone first-30s picture = `plot_early30.py`: per-arm median line + 95%
     bootstrap-CI-of-the-median BAND (all 20 reps, grid-resample + tail-mask) + the 2 measured dots
     (`two_dots`: median first-sample + median at 30s). --metric raw for symcc (raw==excl), excl for
     validation; --manifest keeps colors/order matching the main graphs; emits linear + a `_logx`
     (symlog) companion that exposes the sub-second rise. The CI band is clearly visible here (widest
     during the rise, converged by 30s) — which is impossible on the full-hour axis (first 30s <1% width).
Deliverables: graphs_20260813/overlaid_early/{symcc,validation}/{<name>_overlaid[_zoom].png (plain),
<name>_first30s[_logx].png (separate zoom)}.
REJECTED iterations (do not revisit): ~20 floating dots on the main axes; symlog main axis + stripped
markers + suppressed origin; 2 dots with error BARS ("CI like the rest of the graph"=a shaded BAND, not
bars); early band crammed onto the linear full axis (invisible); the inset-in-corner version.
The --early/--inset-rect/--xscale options still exist in plot_over_time*.py but the SEPARATE-picture
route (plain overlaid + plot_early30) is the deliverable.
- To re-render you must assemble a plot ROOT: <root>/<arm>/coverage/rep_NN_over_time.json (guided hw
  from graphs-20260813/covdata/<run>/<hw-arm>/coverage — the non-lossy regen; fused sz arms from the
  run's results/<arm>/coverage) + <arm>/throughput/rep_NN.json (all from results/<arm>/throughput) +
  manifest.json. Deliverables: .../graphs-20260813/overlaid_early/{symcc,validation}/{symcc_covered,val_excluded}_overlaid_early[_zoom].png.
