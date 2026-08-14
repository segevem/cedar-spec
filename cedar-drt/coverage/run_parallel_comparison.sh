#!/bin/bash
# Run multiple generators + fuzzer in parallel, polling coverage via SIGUSR1.
# All run for the same wall-clock time with snapshots at the same intervals.
#
# Usage:
#   bash run_parallel_comparison.sh [DURATION] [INTERVAL]
#   bash run_parallel_comparison.sh 600 30

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DURATION=${1:-600}
INTERVAL=${2:-30}

LLVM_PROFDATA=$(find "$(rustc --print sysroot)" -name llvm-profdata 2>/dev/null | head -1)
LLVM_COV=$(find "$(rustc --print sysroot)" -name llvm-cov 2>/dev/null | head -1)
GEN_BIN="$SCRIPT_DIR/target/release/cedar-drt-coverage"
FUZZ_BIN="$SCRIPT_DIR/../fuzz/target/x86_64-unknown-linux-gnu/release/validation-drt"
LEAN_LIB=/local/home/segevem/.elan/toolchains/leanprover--lean4---v4.30.0-rc1/lib/lean

OUTPUT_DIR="$SCRIPT_DIR/coverage_results"
rm -rf "$OUTPUT_DIR" 2>/dev/null || true
mkdir -p "$OUTPUT_DIR"

# Build generator with selective coverage (only cedar-policy crates instrumented)
echo "Building generator with selective coverage instrumentation..."
touch "$SCRIPT_DIR/src/main.rs"
RUSTC_WRAPPER="$SCRIPT_DIR/rustc_selective_cov.sh" cargo build --release 2>&1 | tail -2

GENERATORS=("undirected")
PIDS=()
PROFRAW_FILES=()
BINS=()
NAMES=()

# Start all generators
for gen in "${GENERATORS[@]}"; do
    DIR="$OUTPUT_DIR/$gen"
    mkdir -p "$DIR"
    PROF="$DIR/live.profraw"
    rm -f "$PROF"

    LLVM_PROFILE_FILE="$PROF" "$GEN_BIN" \
        --generator "$gen" \
        --duration "$DURATION" \
        --seed 0 \
        --report-interval 999999999 &
    PID=$!
    PIDS+=($PID)
    PROFRAW_FILES+=("$PROF")
    BINS+=("$GEN_BIN")
    NAMES+=("$gen")
    echo "Started $gen (PID=$PID)"
done

# Start fuzzer — runs in short segments matching INTERVAL so profraw is flushed each poll
FUZZ_DIR="$OUTPUT_DIR/fuzzer"
mkdir -p "$FUZZ_DIR/corpus"
# Seed with existing corpus if available
SEED_CORPUS="$SCRIPT_DIR/../fuzz/corpus/validation-drt"
if [ -d "$SEED_CORPUS" ]; then
    cp "$SEED_CORPUS"/* "$FUZZ_DIR/corpus/" 2>/dev/null || true
    echo "Seeded fuzzer corpus with $(ls "$FUZZ_DIR/corpus" | wc -l) entries"
fi
FUZZ_PROF="$FUZZ_DIR/live.profraw"
rm -f "$FUZZ_PROF"

# Fuzzer wrapper: runs in short bursts (INTERVAL/3) so profraw is ready before each poll.
# Uses a lockfile to prevent the polling script from reading mid-merge.
FUZZ_LOCK="$FUZZ_DIR/merge.lock"
(
    SEG_NUM=0
    ELAPSED=0
    FUZZ_SEG=$((INTERVAL / 3))
    if [ "$FUZZ_SEG" -lt 5 ]; then FUZZ_SEG=5; fi
    while [ $ELAPSED -lt $DURATION ]; do
        REMAINING=$((DURATION - ELAPSED))
        SEG=$((FUZZ_SEG < REMAINING ? FUZZ_SEG : REMAINING))
        LD_LIBRARY_PATH="$LEAN_LIB" \
            LLVM_PROFILE_FILE="$FUZZ_DIR/seg_${SEG_NUM}.profraw" \
            "$FUZZ_BIN" "$FUZZ_DIR/corpus" \
            -max_total_time="$SEG" 2>/dev/null || true
        ELAPSED=$((ELAPSED + SEG))
        SEG_NUM=$((SEG_NUM + 1))
        # Merge under lock: only include completed segments (exclude current)
        (
            flock 9
            find "$FUZZ_DIR" -name "seg_*.profraw" -size +0c | \
                xargs "$LLVM_PROFDATA" merge -sparse -o "${FUZZ_PROF}.tmp" 2>/dev/null && \
                mv "${FUZZ_PROF}.tmp" "$FUZZ_PROF" 2>/dev/null || true
        ) 9>"$FUZZ_LOCK"
    done
) &
FUZZ_PID=$!
PIDS+=($FUZZ_PID)
PROFRAW_FILES+=("$FUZZ_PROF")
BINS+=("$FUZZ_BIN")
NAMES+=("fuzzer")
echo "Started fuzzer (PID=$FUZZ_PID)"

echo ""
echo "=== All processes started. Polling every ${INTERVAL}s for ${DURATION}s ==="
echo ""

# Initialize JSON files
for name in "${NAMES[@]}"; do
    echo "[" > "$OUTPUT_DIR/$name/coverage_over_time.json"
done

FIRST_FLAGS=()
for name in "${NAMES[@]}"; do
    FIRST_FLAGS+=(true)
done

sleep 2  # let processes start

ELAPSED=0
while [ $ELAPSED -lt $DURATION ]; do
    sleep "$INTERVAL"
    ELAPSED=$((ELAPSED + INTERVAL))

    printf "  %4ds |" "$ELAPSED"

    # Signal generators to flush coverage (fuzzer flushes between segments)
    for idx in "${!NAMES[@]}"; do
        if [ "${NAMES[$idx]}" != "fuzzer" ]; then
            kill -USR1 "${PIDS[$idx]}" 2>/dev/null || true
        fi
    done
    sleep 1  # let generator flushes complete

    for idx in "${!NAMES[@]}"; do
        NAME="${NAMES[$idx]}"
        PROF="${PROFRAW_FILES[$idx]}"
        BIN="${BINS[$idx]}"
        JSON="$OUTPUT_DIR/$NAME/coverage_over_time.json"
        PROFDATA="$OUTPUT_DIR/$NAME/live.profdata"

        if [ ! -f "$PROF" ] || [ ! -s "$PROF" ]; then
            printf " %15s:  --  |" "$NAME"
            continue
        fi

        if [ "$NAME" = "fuzzer" ]; then
            # Wait for lock to ensure we don't read during a merge
            (
                flock 9
                cp "$PROF" "$PROFDATA" 2>/dev/null
            ) 9>"$FUZZ_LOCK"
            if [ ! -s "$PROFDATA" ]; then
                printf " %15s:  --  |" "$NAME"
                continue
            fi
        else
            "$LLVM_PROFDATA" merge -sparse "$PROF" -o "$PROFDATA" 2>/dev/null || { printf " %15s: err |" "$NAME"; continue; }
        fi

        SUMMARY=$("$LLVM_COV" export "$BIN" \
            -instr-profile="$PROFDATA" \
            -format=text \
            --ignore-filename-regex='/.cargo/registry|/rustc/' \
            -summary-only 2>/dev/null \
            | python3 -c "
import json, sys
data = json.load(sys.stdin)
tc_cov = tc_tot = v_cov = v_tot = 0
for f in data['data'][0]['files']:
    regions = f['summary']['regions']
    name = f['filename']
    if '/validator' in name:
        v_cov += regions['covered']; v_tot += regions['count']
        bn = name.split('/')[-1]
        if any(k in bn for k in ['typecheck','rbac','expr_iterator','partition','diagnostics','extension']):
            tc_cov += regions['covered']; tc_tot += regions['count']
print(json.dumps({'elapsed_secs':$ELAPSED,'typechecker_covered':tc_cov,'typechecker_total':tc_tot,'typechecker_pct':round(100.0*tc_cov/tc_tot,2) if tc_tot>0 else 0,'validator_covered':v_cov,'validator_total':v_tot,'validator_pct':round(100.0*v_cov/v_tot,2) if v_tot>0 else 0}))
" 2>/dev/null) || { printf " %15s: err |" "$NAME"; continue; }

        TC_PCT=$(echo "$SUMMARY" | python3 -c "import json,sys;print(json.load(sys.stdin)['typechecker_pct'])")

        if [ "${FIRST_FLAGS[$idx]}" = true ]; then
            FIRST_FLAGS[$idx]=false
        else
            echo "," >> "$JSON"
        fi
        echo "  $SUMMARY" >> "$JSON"

        printf " %15s: %5s%% |" "$NAME" "$TC_PCT"
    done
    echo ""
done

# Cleanup
echo ""
echo "Stopping processes..."
for pid in "${PIDS[@]}"; do
    kill "$pid" 2>/dev/null || true
done
wait 2>/dev/null || true

# Close JSON files
for name in "${NAMES[@]}"; do
    echo "]" >> "$OUTPUT_DIR/$name/coverage_over_time.json"
done

echo ""
echo "=== Results ==="
for name in "${NAMES[@]}"; do
    echo "  $name: $OUTPUT_DIR/$name/coverage_over_time.json"
done
