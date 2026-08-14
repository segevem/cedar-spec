#!/bin/bash
# Run a generator and produce cumulative coverage snapshots over time.
#
# The x-axis is "total generation attempts" with wall-clock time recorded.
# Each snapshot records attempts, elapsed time, valid inputs, and coverage.
#
# Usage:
#   ./run_coverage.sh [OPTIONS]
#
# Options:
#   --generator NAME       Generator name (default: type-directed)
#   --attempts N           Total generation attempts (default: 10000)
#   --seed S               Starting seed (default: 0)
#   --batch-size B         Attempts per coverage snapshot (default: 1000)
#   --buffer-size B        PRNG buffer bytes per generation (default: 65536)
#   --output-dir DIR       Where to write results (default: ./coverage_results)
#   --corpus PATH          Corpus directory (required for corpus-replay)
#
# Requires: rustup component add llvm-tools-preview
#
# Output: coverage_results/<generator>/coverage_over_time.json

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

GENERATOR="type-directed"
ATTEMPTS=10000
SEED=0
BATCH_SIZE=1000
BUFFER_SIZE=65536
OUTPUT_DIR="./coverage_results"
CORPUS=""

while [[ $# -gt 0 ]]; do
    case $1 in
        --generator) GENERATOR="$2"; shift 2 ;;
        --attempts) ATTEMPTS="$2"; shift 2 ;;
        --seed) SEED="$2"; shift 2 ;;
        --batch-size) BATCH_SIZE="$2"; shift 2 ;;
        --buffer-size) BUFFER_SIZE="$2"; shift 2 ;;
        --output-dir) OUTPUT_DIR="$2"; shift 2 ;;
        --corpus) CORPUS="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

RESULT_DIR="$OUTPUT_DIR/$GENERATOR"
PROFDATA_DIR="$RESULT_DIR/profraw"
mkdir -p "$RESULT_DIR" "$PROFDATA_DIR"

# Find llvm tools
LLVM_PROFDATA=$(find "$(rustc --print sysroot)" -name llvm-profdata 2>/dev/null | head -1)
LLVM_COV=$(find "$(rustc --print sysroot)" -name llvm-cov 2>/dev/null | head -1)

if [ ! -x "$LLVM_PROFDATA" ] || [ ! -x "$LLVM_COV" ]; then
    echo "ERROR: llvm-tools not found. Install with: rustup component add llvm-tools-preview"
    exit 1
fi

# Build with coverage instrumentation
echo "Building with coverage instrumentation..."
RUSTFLAGS="-C instrument-coverage" cargo build --release 2>&1 | tail -3
BINARY="target/release/cedar-drt-coverage"

if [ ! -x "$BINARY" ]; then
    echo "ERROR: Binary not found at $BINARY"
    exit 1
fi

# Build extra args
EXTRA_ARGS=""
if [ -n "$CORPUS" ]; then
    EXTRA_ARGS="--corpus $CORPUS"
fi

echo "=== Coverage over time: generator=$GENERATOR, attempts=$ATTEMPTS, batch=$BATCH_SIZE ==="

# Clean old profraw files
rm -f "$PROFDATA_DIR"/*.profraw

JSON_FILE="$RESULT_DIR/coverage_over_time.json"
echo "[" > "$JSON_FILE"

FIRST=true
CURRENT_SEED=$SEED
TOTAL_ATTEMPTS=0
TOTAL_VALID=0
BATCH_NUM=0
START_TIME=$(date +%s%N)

while [ "$TOTAL_ATTEMPTS" -lt "$ATTEMPTS" ]; do
    REMAINING=$((ATTEMPTS - TOTAL_ATTEMPTS))
    CURRENT_BATCH=$((BATCH_SIZE < REMAINING ? BATCH_SIZE : REMAINING))

    # Run the generator
    OUTPUT=$(LLVM_PROFILE_FILE="$PROFDATA_DIR/batch_${BATCH_NUM}_%m.profraw" \
        "$BINARY" \
        --generator "$GENERATOR" \
        --iterations "$CURRENT_BATCH" \
        --seed "$CURRENT_SEED" \
        --buffer-size "$BUFFER_SIZE" \
        --report-interval "$CURRENT_BATCH" \
        $EXTRA_ARGS 2>&1)

    TOTAL_ATTEMPTS=$((TOTAL_ATTEMPTS + CURRENT_BATCH))
    CURRENT_SEED=$((CURRENT_SEED + CURRENT_BATCH))
    BATCH_NUM=$((BATCH_NUM + 1))

    # Elapsed time in seconds
    NOW=$(date +%s%N)
    ELAPSED_NS=$((NOW - START_TIME))
    ELAPSED_SECS=$(python3 -c "print(round($ELAPSED_NS / 1e9, 2))")

    # Extract valid count from this batch and accumulate
    VALID_BATCH=$(echo "$OUTPUT" | grep -oP '\d+(?= valid inputs)' || echo "0")
    TOTAL_VALID=$((TOTAL_VALID + VALID_BATCH))

    # Merge all profraw files
    "$LLVM_PROFDATA" merge -sparse "$PROFDATA_DIR"/*.profraw -o "$RESULT_DIR/merged.profdata"

    # Generate JSON coverage summary
    SUMMARY=$("$LLVM_COV" export "$BINARY" \
        -instr-profile="$RESULT_DIR/merged.profdata" \
        -format=text \
        --ignore-filename-regex='/.cargo/registry|/rustc/' \
        -summary-only 2>/dev/null \
        | python3 -c "
import json, sys
data = json.load(sys.stdin)

typechecker_covered = 0
typechecker_total = 0
validator_covered = 0
validator_total = 0

for f in data['data'][0]['files']:
    lines = f['summary']['lines']
    name = f['filename']
    if '/validator' in name:
        validator_covered += lines['covered']
        validator_total += lines['count']
        basename = name.split('/')[-1]
        if any(k in basename for k in ['typecheck', 'rbac', 'expr_iterator', 'partition', 'diagnostics', 'extension']):
            typechecker_covered += lines['covered']
            typechecker_total += lines['count']

print(json.dumps({
    'attempts': $TOTAL_ATTEMPTS,
    'elapsed_secs': $ELAPSED_SECS,
    'valid_inputs': $TOTAL_VALID,
    'typechecker_covered': typechecker_covered,
    'typechecker_total': typechecker_total,
    'typechecker_pct': round(100.0 * typechecker_covered / typechecker_total, 2) if typechecker_total > 0 else 0,
    'validator_covered': validator_covered,
    'validator_total': validator_total,
    'validator_pct': round(100.0 * validator_covered / validator_total, 2) if validator_total > 0 else 0,
}))
")

    if [ "$FIRST" = true ]; then
        FIRST=false
    else
        echo "," >> "$JSON_FILE"
    fi
    echo "  $SUMMARY" >> "$JSON_FILE"

    # Print progress
    echo "  batch $((BATCH_NUM-1)) (${ELAPSED_SECS}s): $(echo "$SUMMARY" | python3 -c "import json,sys; d=json.load(sys.stdin); print(f\"attempts={d['attempts']} valid={d['valid_inputs']} | typechecker: {d['typechecker_pct']}% | validator: {d['validator_pct']}%\")")"
done

echo "]" >> "$JSON_FILE"

echo ""
echo "=== Results written to $JSON_FILE ==="

# Generate final HTML report
"$LLVM_COV" show "$BINARY" \
    -instr-profile="$RESULT_DIR/merged.profdata" \
    -format=html \
    --ignore-filename-regex='/.cargo/registry|/rustc/' \
    -output-dir="$RESULT_DIR/html" 2>/dev/null
echo "HTML report: $RESULT_DIR/html/index.html"
