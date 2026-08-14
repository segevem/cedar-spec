#!/bin/bash
# Run a generator continuously and poll coverage via SIGUSR1.
# No process restarts — single long-running process with periodic snapshots.
#
# Usage:
#   bash run_live_coverage.sh [OPTIONS]
#
# Options:
#   --generator NAME       Generator name (default: type-directed)
#   --duration SECS        Total run time (default: 600)
#   --interval SECS        Poll interval (default: 10)
#   --buffer-size B        Buffer size for generator (default: 65536)
#   --output-dir DIR       Where to write results (default: ./coverage_results)
#   --seed S               Starting seed (default: 0)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

GENERATOR="type-directed"
DURATION=600
INTERVAL=10
BUFFER_SIZE=65536
OUTPUT_DIR="./coverage_results"
SEED=0

while [[ $# -gt 0 ]]; do
    case $1 in
        --generator) GENERATOR="$2"; shift 2 ;;
        --duration) DURATION="$2"; shift 2 ;;
        --interval) INTERVAL="$2"; shift 2 ;;
        --buffer-size) BUFFER_SIZE="$2"; shift 2 ;;
        --output-dir) OUTPUT_DIR="$2"; shift 2 ;;
        --seed) SEED="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

RESULT_DIR="$OUTPUT_DIR/$GENERATOR"
mkdir -p "$RESULT_DIR"

LLVM_PROFDATA=$(find "$(rustc --print sysroot)" -name llvm-profdata 2>/dev/null | head -1)
LLVM_COV=$(find "$(rustc --print sysroot)" -name llvm-cov 2>/dev/null | head -1)
GEN_BIN="$SCRIPT_DIR/target/release/cedar-drt-coverage"
PROFRAW="$RESULT_DIR/live.profraw"
PROFDATA="$RESULT_DIR/live.profdata"

# Build with coverage
echo "Building with coverage instrumentation..."
RUSTFLAGS="-C instrument-coverage" cargo build --release 2>&1 | tail -2

echo "=== Live coverage: generator=$GENERATOR, duration=${DURATION}s, poll every ${INTERVAL}s ==="

# Start the generator in the background
rm -f "$PROFRAW"
LLVM_PROFILE_FILE="$PROFRAW" "$GEN_BIN" \
    --generator "$GENERATOR" \
    --duration "$DURATION" \
    --seed "$SEED" \
    --buffer-size "$BUFFER_SIZE" \
    --report-interval 999999999 &
PID=$!

echo "Started PID=$PID"

# Give it a moment to start
sleep 1

JSON_FILE="$RESULT_DIR/coverage_over_time.json"
echo "[" > "$JSON_FILE"
FIRST=true
ELAPSED=0

while kill -0 $PID 2>/dev/null; do
    sleep "$INTERVAL"
    ELAPSED=$((ELAPSED + INTERVAL))

    # Signal the process to flush coverage
    kill -USR1 $PID 2>/dev/null || break
    sleep 0.5  # give it a moment to write

    # Merge and report
    if [ ! -f "$PROFRAW" ] || [ ! -s "$PROFRAW" ]; then
        continue
    fi

    "$LLVM_PROFDATA" merge -sparse "$PROFRAW" -o "$PROFDATA" 2>/dev/null || continue

    SUMMARY=$("$LLVM_COV" export "$GEN_BIN" \
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
print(json.dumps({'elapsed_secs':$ELAPSED,'typechecker_covered':tc_cov,'typechecker_total':tc_tot,'typechecker_pct':round(100.0*tc_cov/tc_tot,2) if tc_tot>0 else 0,'validator_covered':v_cov,'validator_total':v_tot,'validator_pct':round(100.0*v_cov/v_tot,2) if v_tot>0 else 0}))
" 2>/dev/null) || continue

    if [ "$FIRST" = true ]; then FIRST=false; else echo "," >> "$JSON_FILE"; fi
    echo "  $SUMMARY" >> "$JSON_FILE"
    echo "  ${ELAPSED}s: $(echo "$SUMMARY" | python3 -c "import json,sys;d=json.load(sys.stdin);print(f\"tc={d['typechecker_pct']}% val={d['validator_pct']}%\")")"
done

# Wait for process to finish
wait $PID 2>/dev/null || true

echo "]" >> "$JSON_FILE"
echo ""
echo "=== Results written to $JSON_FILE ==="
