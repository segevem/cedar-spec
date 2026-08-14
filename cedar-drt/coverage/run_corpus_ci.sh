#!/bin/bash
# Generate corpora and replay with in-process source coverage measurement.
# Runs N repetitions in parallel with core pinning, then plots with 95% CI.
#
# Usage:
#   bash run_corpus_ci.sh [RUNS] [DURATION] [LEAN_SIZE]
#   bash run_corpus_ci.sh 5 90 25

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

RUNS=${1:-5}
DURATION=${2:-90}
LEAN_SIZE=${3:-25}

FUZZ_BIN="$SCRIPT_DIR/../fuzz/target/x86_64-unknown-linux-gnu/release/validation-drt-type-directed"
LEAN_LIB=/local/home/segevem/.elan/toolchains/leanprover--lean4---v4.30.0-rc1/lib/lean
SANCOV_BIN="$SCRIPT_DIR/target_sancov/release/cedar-drt-coverage"
COV_BIN="$SCRIPT_DIR/target_cov/release/cedar-drt-coverage"

OUTPUT_DIR="$SCRIPT_DIR/corpus_ci_results"
rm -rf "$OUTPUT_DIR"
mkdir -p "$OUTPUT_DIR"

# Build both binaries
echo "=== Building sancov binary (corpus generation) ==="
CARGO_TARGET_DIR="$SCRIPT_DIR/target_sancov" RUSTC_WRAPPER="$SCRIPT_DIR/rustc_sancov.sh" \
    cargo build --release --features lean-gen 2>&1 | tail -1

echo "=== Building coverage binary (replay measurement) ==="
CARGO_TARGET_DIR="$SCRIPT_DIR/target_cov" RUSTC_WRAPPER="$SCRIPT_DIR/rustc_selective_cov.sh" \
    cargo build --release --features "lean-gen,profraw" 2>&1 | tail -1

echo ""
echo "=== Running $RUNS repetitions in parallel: ${DURATION}s each, lean_size=$LEAN_SIZE ==="

# Single run: generate corpus + replay with in-process measurement
run_single() {
    local RUN_ID=$1
    local SPEC_CORE=$2
    local FUZZ_CORE=$3
    local RUN_DIR="$OUTPUT_DIR/run_$RUN_ID"
    mkdir -p "$RUN_DIR"

    # Generate Specimen corpus
    taskset -c "$SPEC_CORE" env LD_LIBRARY_PATH="$LEAN_LIB" \
        "$SANCOV_BIN" \
        --generator lean-schema-typeof \
        --lean-size "$LEAN_SIZE" \
        --duration "$DURATION" \
        --report-interval 999999 \
        --corpus-dir "$RUN_DIR/specimen_corpus" > "$RUN_DIR/specimen_gen.log" 2>&1

    # Generate Fuzz corpus
    mkdir -p "$RUN_DIR/fuzz_corpus"
    taskset -c "$FUZZ_CORE" env LD_LIBRARY_PATH="$LEAN_LIB" \
        "$FUZZ_BIN" "$RUN_DIR/fuzz_corpus" \
        -max_total_time="$DURATION" > "$RUN_DIR/fuzz_gen.log" 2>&1 || true

    # Replay Specimen corpus
    LD_LIBRARY_PATH="$LEAN_LIB" "$COV_BIN" --replay-proto "$RUN_DIR/specimen_corpus" \
        --replay-output "$RUN_DIR/specimen_cov.json" > "$RUN_DIR/specimen_replay.log" 2>&1

    # Replay Fuzz corpus
    LD_LIBRARY_PATH="$LEAN_LIB" "$COV_BIN" --replay-fuzz "$RUN_DIR/fuzz_corpus" \
        --replay-output "$RUN_DIR/fuzz_cov.json" > "$RUN_DIR/fuzz_replay.log" 2>&1

    echo "  Run $RUN_ID complete (cores $SPEC_CORE,$FUZZ_CORE)"
}

# Launch all runs in parallel (3 cores per run: specimen gen, fuzz gen, then replay sequentially)
PIDS=()
for i in $(seq 1 $RUNS); do
    SPEC_CORE=$(( (i - 1) * 3 ))
    FUZZ_CORE=$(( (i - 1) * 3 + 1 ))
    run_single "$i" "$SPEC_CORE" "$FUZZ_CORE" &
    PIDS+=($!)
done

# Wait for all
for pid in "${PIDS[@]}"; do
    wait "$pid" || true
done

echo ""
echo "=== All $RUNS runs complete ==="
echo "=== Plotting with 95% CI ==="

python3 "$SCRIPT_DIR/plot_corpus_ci.py" "$OUTPUT_DIR" "$RUNS"
