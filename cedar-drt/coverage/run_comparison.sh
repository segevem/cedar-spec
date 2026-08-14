#!/bin/bash
# Compare coverage between the fuzzer and a generator over the same budget.
#
# Runs the fuzzer for --duration seconds, records total executions,
# then runs the generator for the same number of attempts.
# Both are instrumented with source coverage and produce coverage-over-time JSON.
#
# Usage:
#   ./run_comparison.sh [OPTIONS]
#
# Options:
#   --duration SECS        How long to run the fuzzer (default: 120)
#   --generator NAME       Generator to compare against (default: type-directed)
#   --batch-size B         Attempts per coverage snapshot for generator (default: 1000)
#   --buffer-size B        PRNG buffer for generator (default: 65536)
#   --output-dir DIR       Where to write results (default: ./coverage_results)
#   --seed S               Generator starting seed (default: 0)
#
# Requires:
#   - rustup component add llvm-tools-preview
#   - Lean static libs built (source cedar-drt/set_env_vars.sh)
#   - The 'cedar' repo at ./cedar (sibling)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DURATION=120
GENERATOR="type-directed"
BATCH_SIZE=1000
BUFFER_SIZE=65536
OUTPUT_DIR="./coverage_results"
SEED=0

while [[ $# -gt 0 ]]; do
    case $1 in
        --duration) DURATION="$2"; shift 2 ;;
        --generator) GENERATOR="$2"; shift 2 ;;
        --batch-size) BATCH_SIZE="$2"; shift 2 ;;
        --buffer-size) BUFFER_SIZE="$2"; shift 2 ;;
        --output-dir) OUTPUT_DIR="$2"; shift 2 ;;
        --seed) SEED="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

FUZZ_DIR="$SCRIPT_DIR/../fuzz"
LLVM_PROFDATA=$(find "$(rustc --print sysroot)" -name llvm-profdata 2>/dev/null | head -1)
LLVM_COV=$(find "$(rustc --print sysroot)" -name llvm-cov 2>/dev/null | head -1)

if [ ! -x "$LLVM_PROFDATA" ] || [ ! -x "$LLVM_COV" ]; then
    echo "ERROR: llvm-tools not found. Install with: rustup component add llvm-tools-preview"
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

echo "============================================"
echo "  STEP 1: Run fuzzer for ${DURATION}s"
echo "============================================"

FUZZ_RESULT_DIR="$OUTPUT_DIR/fuzzer"
FUZZ_PROFDATA_DIR="$FUZZ_RESULT_DIR/profraw"
mkdir -p "$FUZZ_RESULT_DIR" "$FUZZ_PROFDATA_DIR"

# Build fuzzer with source coverage instrumentation
echo "Building fuzzer with coverage instrumentation..."
cd "$FUZZ_DIR"
RUSTFLAGS="-C instrument-coverage" cargo fuzz build -s none validation-drt 2>&1 | tail -5

# Find the fuzzer binary
FUZZ_BINARY=$(find target -name "validation-drt" -path "*/release/*" -type f -executable 2>/dev/null | head -1)
if [ -z "$FUZZ_BINARY" ]; then
    echo "ERROR: Could not find fuzzer binary"
    exit 1
fi
FUZZ_BINARY="$(realpath "$FUZZ_BINARY")"
echo "Fuzzer binary: $FUZZ_BINARY"

# Run fuzzer with time limit, capturing stderr for stats
rm -f "$FUZZ_PROFDATA_DIR"/*.profraw
echo "Running fuzzer for ${DURATION}s..."
LLVM_PROFILE_FILE="$FUZZ_PROFDATA_DIR/fuzz_%m.profraw" \
    "$FUZZ_BINARY" \
    corpus/validation-drt \
    -max_total_time="$DURATION" \
    2>&1 | tee "$FUZZ_RESULT_DIR/fuzzer.log" | tail -5

# Extract total executions from fuzzer output
# libfuzzer final line looks like: "Done 123456 runs in 120 second(s)"
# or stat lines like: "#123456 DONE   cov: ..."
TOTAL_FUZZ_EXECS=$(grep -oP '#\K\d+(?=\s+DONE)' "$FUZZ_RESULT_DIR/fuzzer.log" | tail -1)
if [ -z "$TOTAL_FUZZ_EXECS" ]; then
    # Try alternative format
    TOTAL_FUZZ_EXECS=$(grep -oP 'Done \K\d+' "$FUZZ_RESULT_DIR/fuzzer.log" | tail -1)
fi
if [ -z "$TOTAL_FUZZ_EXECS" ]; then
    # Fallback: use last #NNN from any stat line
    TOTAL_FUZZ_EXECS=$(grep -oP '^#\K\d+' "$FUZZ_RESULT_DIR/fuzzer.log" | tail -1)
fi

echo ""
echo "Fuzzer completed: $TOTAL_FUZZ_EXECS total executions in ${DURATION}s"

# Merge fuzzer profraw and get coverage
"$LLVM_PROFDATA" merge -sparse "$FUZZ_PROFDATA_DIR"/*.profraw -o "$FUZZ_RESULT_DIR/merged.profdata" 2>/dev/null

FUZZ_COVERAGE=$("$LLVM_COV" export "$FUZZ_BINARY" \
    -instr-profile="$FUZZ_RESULT_DIR/merged.profdata" \
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
print(f'typechecker: {typechecker_covered}/{typechecker_total} ({100*typechecker_covered/typechecker_total:.1f}%)')
print(f'validator:   {validator_covered}/{validator_total} ({100*validator_covered/validator_total:.1f}%)')
print(json.dumps({
    'attempts': int('$TOTAL_FUZZ_EXECS'),
    'duration_secs': $DURATION,
    'typechecker_covered': typechecker_covered,
    'typechecker_total': typechecker_total,
    'typechecker_pct': round(100.0 * typechecker_covered / typechecker_total, 2),
    'validator_covered': validator_covered,
    'validator_total': validator_total,
    'validator_pct': round(100.0 * validator_covered / validator_total, 2),
}))
")
echo "Fuzzer coverage: $FUZZ_COVERAGE"

# Save fuzzer result
echo "$FUZZ_COVERAGE" | tail -1 > "$FUZZ_RESULT_DIR/summary.json"

echo ""
echo "============================================"
echo "  STEP 2: Run generator for $TOTAL_FUZZ_EXECS attempts"
echo "============================================"
cd "$SCRIPT_DIR"

./run_coverage.sh \
    --generator "$GENERATOR" \
    --attempts "$TOTAL_FUZZ_EXECS" \
    --batch-size "$BATCH_SIZE" \
    --buffer-size "$BUFFER_SIZE" \
    --output-dir "$OUTPUT_DIR" \
    --seed "$SEED"

echo ""
echo "============================================"
echo "  COMPARISON SUMMARY"
echo "============================================"
echo "Budget: $TOTAL_FUZZ_EXECS attempts (fuzzer ran ${DURATION}s)"
echo ""
echo "Fuzzer:"
echo "  $FUZZ_COVERAGE" | head -2
echo ""
echo "Generator ($GENERATOR):"
tail -3 "$OUTPUT_DIR/$GENERATOR/coverage_over_time.json" | python3 -c "
import json, sys
lines = sys.stdin.read().strip().rstrip(']').rstrip(',').strip()
d = json.loads(lines)
print(f\"  typechecker: {d['typechecker_covered']}/{d['typechecker_total']} ({d['typechecker_pct']}%)\")
print(f\"  validator:   {d['validator_covered']}/{d['validator_total']} ({d['validator_pct']}%)\")
"
