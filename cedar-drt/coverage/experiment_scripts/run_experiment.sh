#!/bin/bash
#
# Multi-run generator-comparison experiment with bootstrap CIs.
#
# Runs REPS independent repetitions of each approach IN PARALLEL, each rep using
# a distinct start seed so its corpus is a disjoint, independent sample (the Lean
# generator additionally SplitMix-diffuses every seed, so runs are statistically
# independent -> honest bootstrap CIs). Then analyzes every rep and hands the
# per-rep metrics to bootstrap_ci.py, which computes the 95% bootstrap CI around
# the MEDIAN for each approach/metric.
#
# Every knob below is overridable from the environment, e.g.:
#   REPS=10 STORAGE=local VALID_COUNT=3000 ./run_experiment.sh
#
# Reproducibility: the exact settings + per-rep seeds + git commit are recorded
# to $OUT/manifest.json. Re-running with the same SEED_BASE reproduces the runs.
set -u

# ------------------------------- settings ----------------------------------
# One config file drives everything. Point CONFIG at a file to override any knob
# below (and/or define the APPROACHES array). Precedence: environment > CONFIG >
# built-in defaults (the example config uses `: "${VAR:=...}"` so env still wins).
CONFIG="${CONFIG:-}"
[[ -n "$CONFIG" && -f "$CONFIG" ]] && { echo "sourcing config: $CONFIG"; source "$CONFIG"; }

COVERAGE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="$(cd "$COVERAGE_DIR/../.." && pwd)"
# Two binary roles: (1) throughput + collect use the UNINSTRUMENTED `$BIN` (specimen) or
# the sancov guided fuzz target (handwritten --guided) — collect just streams the corpus +
# computes metrics, no coverage. (2) LINE coverage for EVERY approach comes from replaying
# that corpus through `$BIN_DRT_COV` = cedar-drt-coverage built with instrument-coverage on
# ONLY the cedar-policy crates (RUSTC_WRAPPER) + reset-once cumulative counters.
BIN="${BIN:-$COVERAGE_DIR/target/release/cedar-experiment}"
BIN_DRT_COV="${BIN_DRT_COV:-$COVERAGE_DIR/target_cov/release/cedar-drt-coverage}"
FUZZ_DIR="${FUZZ_DIR:-$REPO_ROOT/cedar-drt/fuzz}"
FUZZ_BIN_DIR="${FUZZ_BIN_DIR:-$FUZZ_DIR/target/x86_64-unknown-linux-gnu/release}"

REPS="${REPS:-5}"                        # <-- runs per approach (the CI sample size)
TARGET="${TARGET:-validation-drt}"       # validation-drt | rust-only | level-validation-drt | symcc-term-never-errors
export TARGET                            # coverage_analyze.py reads $TARGET to drive the replay oracle (--target)
RUN_SECS="${RUN_SECS:-}"                 # target collect run length; N = rate*RUN_SECS per approach.
                                         #   e.g. 3600 (1h), 43200 (12h). Empty => N = throughput count.
DURATION="${DURATION:-${RUN_SECS:-300}}" # throughput window: defaults to RUN_SECS so the rate is measured
                                         #   over a window as long as the run (representative sizing);
                                         #   falls back to 300 only when RUN_SECS is unset.
VALID_COUNT="${VALID_COUNT:-}"           # fixed N per rep; overrides throughput/RUN_SECS sizing entirely
SEED_BASE="${SEED_BASE:-0}"              # master seed; rep i uses SEED_BASE + i*SEED_STRIDE
SEED_STRIDE="${SEED_STRIDE:-1000000000}" # spacing between rep seeds (must exceed max N -> disjoint)
STORAGE="${STORAGE:-s3}"                 # s3 | local
BUCKET="${BUCKET:-__S3_BUCKET__}"
S3ROOT="${S3ROOT:-typecheck-ci-$(printf '%s' "${EXP_TAG:-run}")}"
OUT="${OUT:-$COVERAGE_DIR/exp_ci_results}"
CPU_PIN="${CPU_PIN:-1}"
BOOTSTRAP="${BOOTSTRAP:-10000}"          # bootstrap resamples (passed to bootstrap_ci.py)
# Coverage replay is the analysis long-pole: it re-runs the faithful DRT (Lean per input)
# over every valid input, and per-rep it is ~single-threaded, so with only ~reps procs the
# box sits mostly idle. REPLAY_SHARDS splits EACH rep's replay into N contiguous batch-shards
# run in parallel (profraw-merged back per rep) — the flattened (approach x rep x shard) pool
# then saturates all cores. It's ALSO the coverage over-time curve resolution (one point per
# shard). 16 => good load-balance + a 16-point curve; raise it for finer curves / more units.
REPLAY_SHARDS="${REPLAY_SHARDS:-16}"
AWS_PROFILE_NAME="${AWS_PROFILE:-cedar-experiment}"

NCORES="$(nproc 2>/dev/null || echo 8)"
MAX_PARALLEL="${MAX_PARALLEL:-$(( NCORES > 2 ? NCORES - 1 : 1 ))}"

# Approaches: "name generator strategy lean_size [fuzz_target]".  generator is one
# of the cedar-experiment --generator values; strategy is the Specimen variant.
# Handwritten (unguided) uses generator=type-directed (strategy ignored).
# A 5th column = a cargo-fuzz target name (e.g. validation-drt-type-directed or
# validation-welltyped-drt) marks the approach as GUIDED: coverage-guided libFuzzer
# for throughput/collect, and coverage via corpus REPLAY (not fused). Omit it (or "-")
# for the unguided/fused path. A single run must be all-guided OR all-fused (the two
# use different instrumented binaries — see the mode check below).
# Source order: APPROACHES_FILE (one entry per line, '#' comments ok) wins —
# used by the EC2 path since bash arrays can't cross `env` to a child process;
# else a preset APPROACHES array; else the built-in default list.
if [[ -n "${APPROACHES_FILE:-}" && -f "${APPROACHES_FILE}" ]]; then
  APPROACHES=()
  while IFS= read -r line; do
    [[ -z "$line" || "$line" =~ ^[[:space:]]*# ]] && continue
    APPROACHES+=("$line")
  done < "$APPROACHES_FILE"
elif [[ -z "${APPROACHES_SET:-}" ]]; then
  APPROACHES=(
    "handwritten          type-directed       budget-aware  20"
    "steep-tags-sz12      lean-schema-typeof  steep-tags    12"
    "steep-tags-sz20      lean-schema-typeof  steep-tags    20"
    "typeof-check-sz12    lean-schema-typeof  typeof-check  12"
    "typeof-check-sz20    lean-schema-typeof  typeof-check  20"
  )
fi

# --------------------------- preconditions ---------------------------------
# On EC2 the box authenticates via its INSTANCE ROLE — there is no named profile,
# so forcing `AWS_PROFILE=cedar-experiment` makes every `aws` CLI call fail
# ("config profile could not be found"), which previously silently lost every
# profraw upload. Set USE_INSTANCE_ROLE=1 on the box to use the default cred chain.
# Locally we keep the named profile.
if [[ "${USE_INSTANCE_ROLE:-0}" == "1" ]]; then
  unset AWS_PROFILE
else
  export AWS_PROFILE="$AWS_PROFILE_NAME"
fi
source "$REPO_ROOT/cedar-drt/set_env_vars.sh" >/dev/null 2>&1 || \
  source "$COVERAGE_DIR/../set_env_vars.sh" >/dev/null 2>&1 || true

if [[ ! -x "$BIN" ]]; then
  echo "ERROR: cedar-experiment binary not found at $BIN" >&2
  echo "Build it first:  (cd $COVERAGE_DIR && cargo build --release --features lean-gen,s3)" >&2
  exit 1
fi
if [[ -n "$VALID_COUNT" && "$VALID_COUNT" -ge "$SEED_STRIDE" ]]; then
  echo "ERROR: VALID_COUNT ($VALID_COUNT) must be < SEED_STRIDE ($SEED_STRIDE) to keep rep seeds disjoint" >&2
  exit 1
fi
# Start from a CLEAN output dir. Critical for count-match correctness: the fused collect
# reads its target V_t from $OUT/<approach>/throughput/rep_NN.json, and the guided collect
# likewise. A STALE throughput JSON left over from a prior run (or baked into a golden AMI's
# /opt/exp) would be read as the target, so collect matches an old (e.g. 30s-smoke) count and
# stops almost immediately instead of running the full window. Wiping $OUT guarantees collect
# only ever sees THIS run's fresh throughput JSONs (written when each probe completes; collect
# polls until then). Set KEEP_OUT=1 to opt out (e.g. resuming a partial local run).
if [[ "${KEEP_OUT:-0}" != "1" ]]; then
  rm -rf "$OUT"
fi
mkdir -p "$OUT"

ts() { date -u +%H:%M:%S; }
log() { echo "[$(ts)] $*"; }

# Cap concurrency: block until a background slot frees up.
throttle() { while (( $(jobs -rp | wc -l) >= MAX_PARALLEL )); do wait -n; done; }

JOB_IDX=0
launch() { # launch "<cmd...>"  -- pins to a rotating core when CPU_PIN=1
  throttle
  local core=$(( 1 + JOB_IDX % (NCORES > 1 ? NCORES - 1 : 1) ))
  JOB_IDX=$(( JOB_IDX + 1 ))
  if [[ "$CPU_PIN" == "1" ]]; then taskset -c "$core" bash -c "$1" & else bash -c "$1" & fi
}

# Guided iff a non-empty, non-"-" 5th column (the cargo-fuzz target name).
is_guided() { [[ -n "${1:-}" && "${1:-}" != "-" ]]; }

# Mixed guided + fused in ONE run is fully supported: both execute the SAME instrumented
# `ValidationDrt` target (Rust validate + Lean FFI + compare), so their covered (file,line)
# sets are directly comparable even though they come from different instrumented binaries
# (fused = cedar-experiment inline; guided = cedar-drt-coverage replay). coverage_analyze.py
# analyzes each approach with its OWN binary/mode (from manifest.json) and combines the sets.
HAS_GUIDED=0; HAS_FUSED=0; GUIDED_COUNT=0
for a in "${APPROACHES[@]}"; do
  read -r _ _ _ _ ftarget <<<"$a"
  if is_guided "$ftarget"; then HAS_GUIDED=1; GUIDED_COUNT=$((GUIDED_COUNT+1)); else HAS_FUSED=1; fi
done
if (( HAS_GUIDED == 1 )) && [[ "$STORAGE" != "s3" ]]; then
  echo "ERROR: guided approaches require STORAGE=s3 (the valid-input corpus streams to S3 for replay)." >&2
  exit 1
fi
(( HAS_GUIDED == 1 )) && log "experiment includes $GUIDED_COUNT guided approach(es) via cargo-fuzz (coverage via corpus replay)"

# =========================== GUIDED PREP ===================================
# The guided approaches spawn PRE-BUILT cargo-fuzz binaries (sancov, coverage-guided);
# build any that are missing before Phase 1 so the timed throughput probe doesn't pay
# the compile. (user_data_body.sh normally pre-builds these on EC2.)
if (( HAS_GUIDED == 1 )); then
  declare -A _FT_SEEN
  for a in "${APPROACHES[@]}"; do
    read -r _ _ _ _ ftarget <<<"$a"
    is_guided "$ftarget" || continue
    [[ -n "${_FT_SEEN[$ftarget]:-}" ]] && continue
    _FT_SEEN[$ftarget]=1
    if [[ ! -x "$FUZZ_BIN_DIR/$ftarget" ]]; then
      log "GUIDED prep: building fuzz target '$ftarget' (cargo fuzz build -s none)…"
      ( cd "$FUZZ_DIR" && cargo +nightly fuzz build -s none "$ftarget" ) \
        > "$OUT/fuzz_build_${ftarget}.log" 2>&1 \
        || { echo "ERROR: cargo fuzz build failed for $ftarget (see $OUT/fuzz_build_${ftarget}.log)" >&2; exit 1; }
    fi
  done
fi

# ===================== PHASE 2 PREP (instrumented replay binary) ===========
# UNIFIED coverage: collect is ALWAYS uninstrumented (fast, streams corpus + metrics);
# coverage for EVERY approach (specimen + guided) comes from a cheap REPLAY of the streamed
# corpus through ONE instrumented binary — cedar-drt-coverage (lean-gen), driving the actual
# ValidationDrt target with RESET-ONCE cumulative counters (no per-input reset, which is
# what made the old fused-inline collect memory-bound and collapse under parallelism).
# Instrument ONLY the cedar-policy crates (via RUSTC_WRAPPER) — not the generators/FFI/
# harness — so the counter array is small (cheap reset-free reads) and instrument-coverage
# runtime overhead is confined to the code under test.
COV_WRAPPER="$COVERAGE_DIR/experiment_scripts/instrument_cedar_only.sh"
# A symcc-* target needs the `symcc` feature (the SymccTermDrt oracle links cedar-policy-symcc),
# and measures the COMPILER not the validator: instrument only cedar_policy_symcc (+ the bin for
# the profiling-runtime link) and flip the analyze filter to keep cedar-policy-symcc / drop the
# validator. Exported so the instrumented build + the coverage_analyze.py stage inherit them.
# (On EC2 user_data_body.sh already exports these; harmless to re-set for local runs.)
COV_FEATURES="${COV_FEATURES:-profraw,s3,lean-gen}"
if [[ "$TARGET" == symcc-* ]]; then
  COV_FEATURES="$COV_FEATURES,symcc"
  export INSTRUMENT_CRATES="cedar_policy_symcc cedar_drt_coverage"
  export COVERAGE_IGNORE_REGEX='/\.cargo/registry|/rustc/|/tests/|/test/|_test\.rs|/test\.rs|/kpath|cedar-policy-generators|cedar-drt|cedar-lean-ffi|cedar-policy-core|cedar-policy-validator'
fi

# Sound error-only line elision (from the MIR CFG + verified error-construction analysis):
# drop these (file,line) from BOTH covered and total so coverage compares only non-error code,
# and emit a raw-vs-excluded over-time overlay. On by default when the bundled exclude file is
# present; set COVERAGE_EXCLUDE_LINES yourself to override, or COVERAGE_EXCLUDE_LINES= to disable.
if [[ -z "${COVERAGE_EXCLUDE_LINES+x}" && -f "$COVERAGE_DIR/spec_unreachable_exclude.txt" ]]; then
  export COVERAGE_EXCLUDE_LINES="$COVERAGE_DIR/spec_unreachable_exclude.txt"
fi
[[ -n "${COVERAGE_EXCLUDE_LINES:-}" && -f "${COVERAGE_EXCLUDE_LINES}" ]] &&   log "  error-only elision ON: $COVERAGE_EXCLUDE_LINES ($(grep -vc '^#' "$COVERAGE_EXCLUDE_LINES") lines)"
if [[ "${SOURCE_COV:-1}" == "1" && ! -x "$BIN_DRT_COV" ]]; then
  log "PHASE 2 prep: building coverage replay binary cedar-drt-coverage (target_cov, features=$COV_FEATURES, cedar-only instrumentation)…"
  ( cd "$COVERAGE_DIR" && RUSTC_WRAPPER="$COV_WRAPPER" \
      cargo build --release --bin cedar-drt-coverage --features "$COV_FEATURES" --target-dir target_cov ) \
    >> "$OUT/coverage_build.log" 2>&1 || log "  instrumented replay build FAILED (see $OUT/coverage_build.log); coverage disabled"
fi
# Edge-snapshot cadence (seconds): ~30 points over the run so throughput-over-time
# has a curve per rep (was effectively off at 100000s).
EDGE_SNAP_SECS="${EDGE_SNAP_SECS:-$(awk "BEGIN{s=${RUN_SECS:-0}; if(s<1)s=${DURATION:-300}; v=int(s/30); if(v<1)v=1; print v}")}"

# ===================== PHASES 1+2 (true parallel, per-approach) ============
# For EACH rep, a throughput probe and a count-matched collect run at the SAME time on
# SEPARATE pinned cores (2 procs/rep). The probe runs the full window and reports V_t =
# valids at full speed; collect runs UNBOUNDED and stops once it has collected V_t (it is
# SLOWER — logging/coverage/Lean I/O — so it runs PAST the probe until it matches; it does
# NOT cut off when the probe ends). Guided and fused differ only in HOW each side runs:
#   guided : cargo-fuzz throughput + `collect --guided --guided-match-throughput`.
#   fused  : generator throughput + `collect` with COLLECT_MATCH_STATS (computes inline
#            metrics + streams corpus). VALID_COUNT forces fixed N.
# BOTH stream their corpus to S3; coverage for BOTH comes from the Phase 3.5 replay.
PROBE_SECS="${RUN_SECS:-$DURATION}"
if (( HAS_GUIDED == 1 )) && [[ -z "$RUN_SECS" ]]; then
  echo "ERROR: guided runs require RUN_SECS (the throughput probe window / term budget)." >&2; exit 1
fi
if [[ -z "${REUSE_CORPUS_S3ROOT:-}" ]]; then
log "PHASE 1+2: throughput (${PROBE_SECS}s) || count-matched collect, true-parallel per rep (max $MAX_PARALLEL)"
for a in "${APPROACHES[@]}"; do
  read -r name gen strat size ftarget <<<"$a"; mkdir -p "$OUT/$name"
  s3flags=""
  [[ "$STORAGE" == "s3" ]] && s3flags="--s3-bucket $BUCKET --s3-prefix $S3ROOT/$name"
  for (( rep=0; rep<REPS; rep++ )); do
    rr=$(printf '%02d' "$rep")
    if is_guided "$ftarget"; then
      # GUIDED: cargo-fuzz probe (full RUN_SECS) ‖ count-matched streaming collect.
      launch "$BIN throughput --guided --fuzz-target $ftarget --target $TARGET \
        --duration $PROBE_SECS --single-rep $rep --seed-base $SEED_BASE --seed-stride $SEED_STRIDE \
        --output-dir '$OUT/$name' --snapshot-interval 5 > '$OUT/$name/phase1_rep$rr.log' 2>&1"
      launch "$BIN collect --guided --fuzz-target $ftarget --guided-match-throughput \
        --target $TARGET --valid-count 0 --single-rep $rep --seed-base $SEED_BASE --seed-stride $SEED_STRIDE \
        --output-dir '$OUT/$name' $s3flags > '$OUT/$name/phase2_rep$rr.log' 2>&1"
      continue
    fi
    # FUSED (specimen/unguided): generator probe ‖ count-matched collect. COLLECT_STREAM_ONLY
    # keeps collect at ~probe speed (skips the per-input k-path analysis — the ~10x cost that
    # stalled count-match); it just runs the DRT + streams the corpus to S3. Diversity is
    # recomputed by the parallel Phase-3 replay-analyze; coverage by the Phase-3.5 replay.
    tp_json="$OUT/$name/throughput/rep_$rr.json"
    matchenv=""; vc="${VALID_COUNT:-1000}"
    if [[ -z "$VALID_COUNT" ]]; then
      launch "$BIN throughput --generator $gen --strategy $strat --lean-size $size \
        --target $TARGET --duration $PROBE_SECS --single-rep $rep --seed-base $SEED_BASE --seed-stride $SEED_STRIDE \
        --output-dir '$OUT/$name' --snapshot-interval 5 > '$OUT/$name/phase1_rep$rr.log' 2>&1"
      matchenv="COLLECT_MATCH_STATS='$tp_json'"; vc=0
    fi
    # Per-approach WELL-TYPED filter: an approach named `*-filtered` gets the collect-time
    # `COLLECT_WELLTYPED_ONLY` reject gate (drops any input Rust `validate` rejects, same as the
    # welltyped fuzz target's Corpus::Reject). Paired with an identically-seeded unfiltered twin
    # (same generator/strategy/size/seed), a SOUND generator rejects 0 -> byte-identical corpus
    # -> J=1.000 in the compare, confirming no ill-typed inputs slip through the proto round-trip.
    filterenv=""
    [[ "$name" == *-filtered ]] && filterenv="COLLECT_WELLTYPED_ONLY=1"
    launch "COLLECT_STREAM_ONLY=1 $filterenv $matchenv $BIN collect --generator $gen --strategy $strat --lean-size $size \
      --target $TARGET --valid-count $vc --single-rep $rep --seed-base $SEED_BASE --seed-stride $SEED_STRIDE \
      --output-dir '$OUT/$name' --snapshot-interval $EDGE_SNAP_SECS $s3flags \
      > '$OUT/$name/phase2_rep$rr.log' 2>&1"
  done
done
wait
log "PHASE 1+2 done"
else log "REUSE_CORPUS_S3ROOT=$REUSE_CORPUS_S3ROOT — skipping generation (PHASE 1+2)"; fi

# =============================== PHASE 3 ====================================
# ALL approaches now collect STREAM-ONLY (guided: fuzz drain; specimen: COLLECT_STREAM_ONLY)
# — none compute inline diversity metrics. So the replay-analyze is REQUIRED for every
# approach: it replays the S3 corpus and computes k-paths / unique / node counts into
# analyze/rep_NN.json. The analyze is itself rayon-parallel across the corpus (all cores,
# HLL/histogram-bounded memory), so we run approaches SEQUENTIALLY here — each gets the whole
# box rather than N processes oversubscribing cores + multiplying HLL memory.
if [[ -z "${REUSE_CORPUS_S3ROOT:-}" ]]; then
log "PHASE 3: parallel replay-analyze (rayon, all cores) — ${#APPROACHES[@]} approaches x $REPS reps, sequential per approach"
for a in "${APPROACHES[@]}"; do
  read -r name _ _ _ _ <<<"$a"
  if [[ "$STORAGE" == "s3" ]]; then
    src="--s3-bucket $BUCKET --s3-prefix $S3ROOT/$name"
  else
    src=""
  fi
  "$BIN" analyze --format proto --reps "$REPS" $src \
    --output-dir "$OUT/$name" > "$OUT/$name/phase3.log" 2>&1 \
    || log "  analyze failed for $name (see $OUT/$name/phase3.log)"
done
log "PHASE 3 done"
else log "REUSE_CORPUS_S3ROOT=$REUSE_CORPUS_S3ROOT — skipping k-path analyze (PHASE 3)"; fi

# ----------------------------- manifest ------------------------------------
# Written BEFORE coverage so coverage_analyze.py can read per-approach guided/fuzz_target
# and pick the right instrumented binary + mode per approach.
{
  echo "{"
  echo "  \"reps\": $REPS,"
  echo "  \"target\": \"$TARGET\","
  echo "  \"storage\": \"$STORAGE\","
  echo "  \"seed_base\": $SEED_BASE,"
  echo "  \"seed_stride\": $SEED_STRIDE,"
  echo "  \"bootstrap_resamples\": $BOOTSTRAP,"
  echo "  \"git_commit\": \"$(cd "$REPO_ROOT" && git rev-parse HEAD 2>/dev/null || echo unknown)\","
  echo "  \"approaches\": ["
  first=1
  for a in "${APPROACHES[@]}"; do
    read -r name gen strat size ftarget <<<"$a"
    seeds="["; for (( rep=0; rep<REPS; rep++ )); do
      [[ $rep -gt 0 ]] && seeds+=", "; seeds+=$(( SEED_BASE + rep * SEED_STRIDE )); done; seeds+="]"
    if is_guided "$ftarget"; then ftj="\"$ftarget\""; guidedj=true; else ftj="null"; guidedj=false; fi
    [[ $first == 0 ]] && echo ","; first=0
    printf '    {"name": "%s", "generator": "%s", "strategy": "%s", "lean_size": %s, "guided": %s, "fuzz_target": %s, "N": %s, "rep_seeds": %s}' \
      "$name" "$gen" "$strat" "$size" "$guidedj" "$ftj" "${VALID_COUNT:-null}" "$seeds"
  done
  echo ""; echo "  ]"; echo "}"
} > "$OUT/manifest.json"
log "manifest -> $OUT/manifest.json"

# ===================== PHASE 3.5 PREP: S3 upload barrier ====================
# Before the replay lists each rep's S3 corpus, make sure its uploads have SETTLED. The guided
# drain streams batches asynchronously, so if PHASE 3.5 lists a corpus prefix while uploads are
# still in flight, the replay shards stream 0 inputs → that rep's coverage is silently empty
# (observed on ci-run-…041143Z: whole guided reps replayed 0/16 shards even though the corpora
# were fully present moments later). Wait per prefix until it is NON-EMPTY and its object count
# is STABLE across two checks (already-done prefixes clear on the 2nd check in a few seconds).
if [[ "$STORAGE" == "s3" && "${SOURCE_COV:-1}" == "1" && -z "${REUSE_CORPUS_S3ROOT:-}" ]]; then
  log "PHASE 3.5 prep: waiting for S3 corpus uploads to settle before replay"
  for a in "${APPROACHES[@]}"; do
    read -r name _ _ _ _ <<<"$a"
    for (( rep=0; rep<REPS; rep++ )); do
      rr=$(printf '%02d' "$rep")
      pfx="s3://$BUCKET/$S3ROOT/$name/rep_$rr/corpus/"
      prev=-1
      for _t in $(seq 1 40); do
        cnt=$(aws s3 ls "$pfx" 2>/dev/null | grep -c '\.bin')
        [[ "$cnt" -gt 0 && "$cnt" -eq "$prev" ]] && break
        prev=$cnt; sleep 3
      done
      [[ "${prev:-0}" -le 0 ]] && log "  WARN: $name rep_$rr corpus still empty after wait (replay may be partial)"
    done
  done
  log "PHASE 3.5 prep: corpus uploads settled"
fi

# =========================== PHASE 3.5 =====================================
# Input-driven validator LINE coverage (distinct from the guided fuzzer's sancov edge
# coverage). UNIFIED: every approach's streamed corpus is REPLAYED through the ONE
# instrumented cedar-drt-coverage binary (reset-once cumulative, driving the actual
# ValidationDrt target) — so all covered (file,line) sets share one binary + one scope and
# combine into coverage_compare.json. coverage_analyze.py runs the per-rep replays in
# parallel, derives (harness-excluded): line coverage over time (bootstrap-CI'd), per-rep
# `source_lines_covered` (stamped into analyze/rep_NN.json), and the cross-approach diff
# (guided vs specimen, from manifest.json labels). Opt out with SOURCE_COV=0.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [[ "${SOURCE_COV:-1}" == "1" && -x "$BIN_DRT_COV" ]]; then
  s3args=""
  [[ "$STORAGE" == "s3" ]] && s3args="--s3-bucket $BUCKET --s3-root ${REUSE_CORPUS_S3ROOT:-$S3ROOT}"
  log "PHASE 3.5: source line coverage (unified reset-once replay via cedar-drt-coverage; harness excluded)"
  python3 "$SCRIPT_DIR/coverage_analyze.py" --root "$OUT" --manifest "$OUT/manifest.json" \
    --binary "$BIN_DRT_COV" --reps "$REPS" --replay-shards "$REPLAY_SHARDS" $s3args \
    > "$OUT/coverage_analyze.log" 2>&1 && log "  coverage -> $OUT/coverage_compare.json" \
    || log "  coverage_analyze.py failed (see $OUT/coverage_analyze.log)"
fi

# =============================== PHASE 4 ====================================
# Produce the full result set: final-value CI table + panels, over-time CI bands
# for each metric (throughput, 2-/3-paths, unique inputs, line coverage), and the
# coverage overlap/diff chart.
log "PHASE 4: bootstrap CI + plots"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
NAMES=(); for a in "${APPROACHES[@]}"; do read -r name _ _ _ <<<"$a"; NAMES+=("$name"); done

# Final-value median + 95% bootstrap CI (json + panels).
python3 "$SCRIPT_DIR/bootstrap_ci.py" --root "$OUT" --reps "$REPS" \
  --resamples "$BOOTSTRAP" --names "${NAMES[@]}" || echo "bootstrap_ci.py failed (results still in $OUT)"
python3 "$SCRIPT_DIR/plot_ci.py" --root "$OUT" || echo "plot_ci.py skipped/failed"

# Over-time CI bands (median + 95% bootstrap), one PNG per metric.
OT_METRICS="throughput cumulative_3paths cumulative_2paths unique_inputs"
[[ "${SOURCE_COV:-1}" == "1" ]] && OT_METRICS="$OT_METRICS source_lines_covered"
for m in $OT_METRICS; do
  python3 "$SCRIPT_DIR/plot_over_time.py" --root "$OUT" --metric "$m" --reps "$REPS" \
    || echo "over-time plot ($m) skipped/failed"
done
# Raw-vs-error-excluded coverage-over-time OVERLAY (covered_lines vs covered_lines_excl).
[[ "${SOURCE_COV:-1}" == "1" ]] && { python3 "$SCRIPT_DIR/plot_over_time_excl.py" --root "$OUT" --reps "$REPS" \
    || echo "over-time excluded-overlay plot skipped/failed"; }

# Coverage overlap/diff chart (shared / only-specimen / only-handwritten + by-function).
if [[ "${SOURCE_COV:-1}" == "1" ]]; then
  python3 "$SCRIPT_DIR/plot_coverage_compare.py" --root "$OUT" \
    || echo "coverage_compare plot skipped/failed"
  # Coverage treemap (which regions of the program are uncovered): area=region-lines,
  # color=covered%, grouped by module. One per coverage-map side.
  for which in specimen_union handwritten_union; do
    python3 "$SCRIPT_DIR/plot_coverage_treemap.py" --root "$OUT" --which "$which" \
      || echo "coverage_treemap ($which) skipped/failed"
  done
  # Differential treemap: which regions specimen vs handwritten reach UNIQUELY.
  python3 "$SCRIPT_DIR/plot_coverage_treemap.py" --root "$OUT" --mode diff \
    || echo "coverage_treemap (diff) skipped/failed"
fi

log "DONE. In $OUT: bootstrap_ci.{json,png}, over_time_*.png$([[ "${SOURCE_COV:-1}" == "1" ]] && echo ', coverage_compare.{json,png}')"
