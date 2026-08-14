#!/bin/bash
# Run the actual fuzzer and capture source coverage over time.
# Uses SIGURG to trigger __llvm_profile_write_file() mid-run, polling coverage
# from a single long-running process without restarts (preserving libFuzzer state).
#
# Usage:
#   ./run_fuzzer_coverage.sh [OPTIONS]
#
# Options:
#   --duration SECS       Total fuzzer run time (default: 120)
#   --interval SECS       Poll interval for coverage snapshots (default: 10)
#   --output-dir DIR      Where to write results (default: ./coverage_results)
#   --skip-build          Use existing binary without rebuilding

set -euo pipefail
setopt null_glob 2>/dev/null || shopt -s nullglob 2>/dev/null || true

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DURATION=120
INTERVAL=10
OUTPUT_DIR="./coverage_results"
SKIP_BUILD=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --duration) DURATION="$2"; shift 2 ;;
        --interval) INTERVAL="$2"; shift 2 ;;
        --output-dir) OUTPUT_DIR="$2"; shift 2 ;;
        --skip-build) SKIP_BUILD=true; shift ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

# Source Lean env
source "$SCRIPT_DIR/../set_env_vars.sh"

FUZZ_DIR="$SCRIPT_DIR/../fuzz"
RESULT_DIR="$OUTPUT_DIR/fuzzer"
PROFDATA_DIR="$RESULT_DIR/profraw"
CORPUS_DIR="$RESULT_DIR/corpus"
mkdir -p "$RESULT_DIR" "$PROFDATA_DIR" "$CORPUS_DIR"

# Find llvm tools
LLVM_PROFDATA=$(find "$(rustc --print sysroot)" -name llvm-profdata 2>/dev/null | head -1)
LLVM_COV=$(find "$(rustc --print sysroot)" -name llvm-cov 2>/dev/null | head -1)

if [ ! -x "$LLVM_PROFDATA" ] || [ ! -x "$LLVM_COV" ]; then
    echo "ERROR: llvm-tools not found. Install with: rustup component add llvm-tools-preview"
    exit 1
fi

FUZZ_BIN="$FUZZ_DIR/target/x86_64-unknown-linux-gnu/release/validation-drt"

if [ "$SKIP_BUILD" = false ]; then
    # Build fuzzer with source coverage instrumentation
    echo "Building fuzzer with source coverage instrumentation..."
    cd "$FUZZ_DIR"
    RUSTFLAGS="-C instrument-coverage -Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-level=4 -Cllvm-args=-sanitizer-coverage-inline-8bit-counters -Cllvm-args=-sanitizer-coverage-pc-table -Cllvm-args=-sanitizer-coverage-trace-compares --cfg fuzzing -Cllvm-args=-simplifycfg-branch-fold-threshold=0 -Cllvm-args=-sanitizer-coverage-stack-depth -Cdebug-assertions -Ccodegen-units=1" \
        cargo build --manifest-path Cargo.toml --target x86_64-unknown-linux-gnu --release --bin validation-drt 2>&1 | tail -3
fi

if [ ! -x "$FUZZ_BIN" ]; then
    echo "ERROR: Fuzzer binary not found at $FUZZ_BIN"
    exit 1
fi

cd "$SCRIPT_DIR"

echo "=== Fuzzer coverage over time: duration=${DURATION}s, poll every ${INTERVAL}s ==="

# Clean old profraw
rm -f "$PROFDATA_DIR"/*

PROFRAW="$PROFDATA_DIR/fuzz_%m.profraw"

# Start the fuzzer in the background.
# The binary has a SIGURG handler that calls __llvm_profile_write_file(),
# so we can flush coverage mid-run without restarting — critical for stateful
# fuzzing where process restarts destroy libFuzzer's internal state.
LLVM_PROFILE_FILE="$PROFRAW" "$FUZZ_BIN" "$CORPUS_DIR" \
    -max_total_time="$DURATION" \
    2>"$RESULT_DIR/fuzzer.log" &
PID=$!

echo "Started fuzzer PID=$PID"
sleep 1

JSON_FILE="$RESULT_DIR/coverage_over_time.json"
echo "[" > "$JSON_FILE"
FIRST=true
ELAPSED=0

while kill -0 $PID 2>/dev/null; do
    sleep "$INTERVAL"
    ELAPSED=$((ELAPSED + INTERVAL))

    # Signal the fuzzer to flush coverage via SIGURG handler
    kill -URG $PID 2>/dev/null || break
    sleep 0.5

    PROFRAW_FILES=$(find "$PROFDATA_DIR" -name "*.profraw" 2>/dev/null)
    if [ -z "$PROFRAW_FILES" ]; then
        continue
    fi

    "$LLVM_PROFDATA" merge -sparse $PROFRAW_FILES -o "$RESULT_DIR/merged.profdata" 2>/dev/null || continue

    # Extract run count from fuzzer stderr log
    TOTAL_RUNS=$(grep -oP '^#\K\d+' "$RESULT_DIR/fuzzer.log" | tail -1 || echo "0")

    SUMMARY=$("$LLVM_COV" export "$FUZZ_BIN" \
        -instr-profile="$RESULT_DIR/merged.profdata" \
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
        basename = name.split('/')[-1]
        if any(k in basename for k in ['typecheck','rbac','expr_iterator','partition','diagnostics','extension']):
            tc_cov += lines['covered']; tc_tot += lines['count']
print(json.dumps({
    'attempts': int('$TOTAL_RUNS') if '$TOTAL_RUNS' != '0' else 0,
    'elapsed_secs': $ELAPSED,
    'typechecker_covered': tc_cov,
    'typechecker_total': tc_tot,
    'typechecker_pct': round(100.0*tc_cov/tc_tot, 2) if tc_tot > 0 else 0,
    'validator_covered': v_cov,
    'validator_total': v_tot,
    'validator_pct': round(100.0*v_cov/v_tot, 2) if v_tot > 0 else 0,
}))
" 2>/dev/null) || continue

    if [ "$FIRST" = true ]; then FIRST=false; else echo "," >> "$JSON_FILE"; fi
    echo "  $SUMMARY" >> "$JSON_FILE"
    echo "  ${ELAPSED}s: $(echo "$SUMMARY" | python3 -c "import json,sys;d=json.load(sys.stdin);print(f\"runs={d['attempts']} | typechecker: {d['typechecker_pct']}% | validator: {d['validator_pct']}%\")")"
done

# Wait for fuzzer to finish
wait $PID 2>/dev/null || true

echo "]" >> "$JSON_FILE"

TOTAL_RUNS=$(grep -oP '^#\K\d+' "$RESULT_DIR/fuzzer.log" | tail -1 || echo "?")
echo ""
echo "=== Fuzzer results written to $JSON_FILE ==="
echo "Total: $TOTAL_RUNS executions in ${DURATION}s"
