#!/bin/bash
# Run the full comparison multiple times IN PARALLEL with core pinning.
# Each run gets its own pair of cores and output directory.
#
# Usage:
#   bash run_repeated_comparison.sh [RUNS] [DURATION] [SEGMENT] [GENERATOR]
#   bash run_repeated_comparison.sh 5 300 30 lean-schema-typeof

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

RUNS=${1:-5}
DURATION=${2:-300}
SEGMENT=${3:-30}
GENERATOR=${4:-lean-schema-typeof}

RESULTS_DIR="$SCRIPT_DIR/repeated_results"
rm -rf "$RESULTS_DIR"
mkdir -p "$RESULTS_DIR"

# Build once upfront (shared binary)
FEATURES=""
if [[ "$GENERATOR" == "lean-typeof" || "$GENERATOR" == "lean-schema-typeof" ]]; then
    FEATURES="--features lean-gen"
fi
echo "Building generator with coverage instrumentation... ${FEATURES}"
RUSTFLAGS="-C instrument-coverage" cargo build --release $FEATURES 2>&1 | tail -3

FUZZ_BIN="${FUZZ_BIN:-$SCRIPT_DIR/../fuzz/target/x86_64-unknown-linux-gnu/release/validation-drt-type-directed}"
GEN_BIN="$SCRIPT_DIR/target/release/cedar-drt-coverage"
LLVM_PROFDATA=$(find "$(rustc --print sysroot)" -name llvm-profdata 2>/dev/null | head -1)
LLVM_COV=$(find "$(rustc --print sysroot)" -name llvm-cov 2>/dev/null | head -1)
LEAN_LIB=/local/home/segevem/.elan/toolchains/leanprover--lean4---v4.30.0-rc1/lib/lean
NUM_SEGMENTS=$((DURATION / SEGMENT))

NPROC=$(nproc)
# Each run needs ~2 cores (fuzzer + generator run sequentially within a run)
MAX_PARALLEL=$((NPROC / 2))
if [ "$RUNS" -lt "$MAX_PARALLEL" ]; then
    MAX_PARALLEL=$RUNS
fi

echo "=== Running $RUNS repetitions in parallel (max $MAX_PARALLEL concurrent): ${DURATION}s, ${SEGMENT}s segments, generator=$GENERATOR ==="

# Helper: extract coverage from a profdata file for a given binary
coverage_json() {
    local BIN="$1"
    local PROFDATA="$2"
    local ELAPSED="$3"
    local ATTEMPTS="$4"
    local VALID="$5"
    "$LLVM_COV" export "$BIN" \
        -instr-profile="$PROFDATA" \
        -format=text \
        --ignore-filename-regex='/.cargo/registry|/rustc/' \
        -summary-only 2>/dev/null \
        | python3 -c "
import json, sys
data = json.load(sys.stdin)
tc_cov = tc_tot = v_cov = v_tot = 0
for f in data['data'][0]['files']:
    lines = f['summary']['lines']
    name = f['filename']
    if '/validator' in name:
        v_cov += lines['covered']; v_tot += lines['count']
        bn = name.split('/')[-1]
        if any(k in bn for k in ['typecheck','rbac','expr_iterator','partition','diagnostics','extension']):
            tc_cov += lines['covered']; tc_tot += lines['count']
print(json.dumps({'elapsed_secs':$ELAPSED,'attempts':$ATTEMPTS,'valid_inputs':$VALID,'typechecker_covered':tc_cov,'typechecker_total':tc_tot,'typechecker_pct':round(100.0*tc_cov/tc_tot,2) if tc_tot>0 else 0,'validator_covered':v_cov,'validator_total':v_tot,'validator_pct':round(100.0*v_cov/v_tot,2) if v_tot>0 else 0}))
"
}

# Run the fuzzer half of a single comparison
run_fuzzer() {
    local RUN_DIR=$1
    local CORE=$2
    mkdir -p "$RUN_DIR/fuzzer/profraw" "$RUN_DIR/fuzzer/corpus"
    echo "[" > "$RUN_DIR/fuzzer/coverage_over_time.json"
    local FIRST=true
    local FUZZ_TOTAL_RUNS=0
    for i in $(seq 1 $NUM_SEGMENTS); do
        OUTPUT=$(taskset -c "$CORE" env LD_LIBRARY_PATH="$LEAN_LIB" \
            LLVM_PROFILE_FILE="$RUN_DIR/fuzzer/profraw/seg${i}_%m.profraw" \
            "$FUZZ_BIN" "$RUN_DIR/fuzzer/corpus" \
            -max_total_time="$SEGMENT" 2>&1 || true)
        RUNS_THIS=$(echo "$OUTPUT" | grep -oP 'Done \K\d+' | tail -1)
        RUNS_THIS=${RUNS_THIS:-0}
        FUZZ_TOTAL_RUNS=$((FUZZ_TOTAL_RUNS + RUNS_THIS))
        ELAPSED=$((i * SEGMENT))
        find "$RUN_DIR/fuzzer/profraw" -name "*.profraw" | xargs "$LLVM_PROFDATA" merge -sparse -o "$RUN_DIR/fuzzer/merged.profdata" 2>/dev/null
        CORPUS_SIZE=$(find "$RUN_DIR/fuzzer/corpus" -type f | wc -l)
        SUMMARY=$(coverage_json "$FUZZ_BIN" "$RUN_DIR/fuzzer/merged.profdata" "$ELAPSED" "$FUZZ_TOTAL_RUNS" "$CORPUS_SIZE")
        if [ "$FIRST" = true ]; then FIRST=false; else echo "," >> "$RUN_DIR/fuzzer/coverage_over_time.json"; fi
        echo "  $SUMMARY" >> "$RUN_DIR/fuzzer/coverage_over_time.json"
    done
    echo "]" >> "$RUN_DIR/fuzzer/coverage_over_time.json"
}

# Run the generator half of a single comparison
run_generator() {
    local RUN_DIR=$1
    local CORE=$2
    mkdir -p "$RUN_DIR/$GENERATOR/profraw"
    echo "[" > "$RUN_DIR/$GENERATOR/coverage_over_time.json"
    local FIRST=true
    local GEN_SEED=0
    local GEN_TOTAL_ATTEMPTS=0
    local GEN_TOTAL_VALID=0
    for i in $(seq 1 $NUM_SEGMENTS); do
        OUTPUT=$(taskset -c "$CORE" env \
            LLVM_PROFILE_FILE="$RUN_DIR/$GENERATOR/profraw/seg${i}_%m.profraw" \
            "$GEN_BIN" \
            --generator "$GENERATOR" \
            --duration "$SEGMENT" \
            --seed "$GEN_SEED" \
            --buffer-size 65536 \
            --report-interval 999999999 2>&1)
        ATTEMPTS=$(echo "$OUTPUT" | grep -oP '\d+(?= attempts in)' | tail -1)
        ATTEMPTS=${ATTEMPTS:-0}
        VALID=$(echo "$OUTPUT" | grep -oP '\d+(?= valid inputs)' | tail -1)
        VALID=${VALID:-0}
        GEN_TOTAL_ATTEMPTS=$((GEN_TOTAL_ATTEMPTS + ATTEMPTS))
        GEN_TOTAL_VALID=$((GEN_TOTAL_VALID + VALID))
        GEN_SEED=$((GEN_SEED + ATTEMPTS))
        ELAPSED=$((i * SEGMENT))
        find "$RUN_DIR/$GENERATOR/profraw" -name "*.profraw" | xargs "$LLVM_PROFDATA" merge -sparse -o "$RUN_DIR/$GENERATOR/merged.profdata" 2>/dev/null
        SUMMARY=$(coverage_json "$GEN_BIN" "$RUN_DIR/$GENERATOR/merged.profdata" "$ELAPSED" "$GEN_TOTAL_ATTEMPTS" "$GEN_TOTAL_VALID")
        if [ "$FIRST" = true ]; then FIRST=false; else echo "," >> "$RUN_DIR/$GENERATOR/coverage_over_time.json"; fi
        echo "  $SUMMARY" >> "$RUN_DIR/$GENERATOR/coverage_over_time.json"
    done
    echo "]" >> "$RUN_DIR/$GENERATOR/coverage_over_time.json"
}

# Run a single comparison: fuzzer and generator in parallel on separate cores
run_single() {
    local RUN_ID=$1
    local FUZZ_CORE=$2
    local GEN_CORE=$3
    local RUN_DIR="$RESULTS_DIR/run_$RUN_ID"
    mkdir -p "$RUN_DIR"

    run_fuzzer "$RUN_DIR" "$FUZZ_CORE" &
    local FUZZ_PID=$!
    run_generator "$RUN_DIR" "$GEN_CORE" &
    local GEN_PID=$!

    wait $FUZZ_PID
    wait $GEN_PID
    echo "  Run $RUN_ID complete (cores $FUZZ_CORE,$GEN_CORE)"
}

# Launch runs in parallel with core pinning (2 cores per run)
PIDS=()
for i in $(seq 1 $RUNS); do
    FUZZ_CORE=$(( (i - 1) * 2 ))
    GEN_CORE=$(( (i - 1) * 2 + 1 ))
    run_single "$i" "$FUZZ_CORE" "$GEN_CORE" &
    PIDS+=($!)
    # Throttle if we've hit max parallel
    if [ ${#PIDS[@]} -ge $MAX_PARALLEL ]; then
        wait "${PIDS[0]}"
        PIDS=("${PIDS[@]:1}")
    fi
done

# Wait for remaining
for pid in "${PIDS[@]}"; do
    wait "$pid"
done

echo ""
echo "=== All $RUNS runs complete. Results in: $RESULTS_DIR ==="
echo "Plot with: python3 plot_ci_comparison.py $RESULTS_DIR"
