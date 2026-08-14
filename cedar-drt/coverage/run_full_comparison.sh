#!/bin/bash
# Compare fuzzer vs generator over the same wall-clock time.
# Both run for DURATION seconds, with coverage snapshots every SEGMENT seconds.
# Primary x-axis: elapsed time. Also reports attempts and valid inputs.
#
# Usage:
#   bash run_full_comparison.sh [DURATION] [SEGMENT] [GENERATOR] [BUFFER_SIZE]
#   bash run_full_comparison.sh 120 10 type-directed 65536

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DURATION=${1:-120}
SEGMENT=${2:-10}
GENERATOR=${3:-type-directed}
BUFFER_SIZE=${4:-65536}

FUZZ_BIN="${FUZZ_BIN:-$SCRIPT_DIR/../fuzz/target/x86_64-unknown-linux-gnu/release/validation-drt-type-directed}"
LLVM_PROFDATA=$(find "$(rustc --print sysroot)" -name llvm-profdata 2>/dev/null | head -1)
LLVM_COV=$(find "$(rustc --print sysroot)" -name llvm-cov 2>/dev/null | head -1)
LEAN_LIB=/local/home/segevem/.elan/toolchains/leanprover--lean4---v4.30.0-rc1/lib/lean

OUTPUT_DIR="$SCRIPT_DIR/coverage_results"
rm -rf "$OUTPUT_DIR"

# Build generator with coverage instrumentation
# Use --features lean-gen if the generator requires the Lean FFI
FEATURES=""
if [[ "$GENERATOR" == "lean-typeof" || "$GENERATOR" == "lean-schema-typeof" ]]; then
    FEATURES="--features lean-gen"
fi
echo "Building generator with coverage instrumentation... ${FEATURES}"
RUSTFLAGS="-C instrument-coverage" cargo build --release $FEATURES 2>&1 | tail -3
GEN_BIN="$SCRIPT_DIR/target/release/cedar-drt-coverage"

NUM_SEGMENTS=$((DURATION / SEGMENT))

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

# =========== FUZZER ===========
echo ""
echo "========== FUZZER (${DURATION}s, ${SEGMENT}s segments) =========="

FUZZ_DIR="$OUTPUT_DIR/fuzzer"
mkdir -p "$FUZZ_DIR/profraw" "$FUZZ_DIR/corpus"

echo "[" > "$FUZZ_DIR/coverage_over_time.json"
FIRST=true
FUZZ_TOTAL_RUNS=0

for i in $(seq 1 $NUM_SEGMENTS); do
    OUTPUT=$(LD_LIBRARY_PATH="$LEAN_LIB" \
        LLVM_PROFILE_FILE="$FUZZ_DIR/profraw/seg${i}_%m.profraw" \
        "$FUZZ_BIN" "$FUZZ_DIR/corpus" \
        -max_total_time="$SEGMENT" 2>&1 || true)

    RUNS=$(echo "$OUTPUT" | grep -oP 'Done \K\d+' | tail -1)
    RUNS=${RUNS:-0}
    FUZZ_TOTAL_RUNS=$((FUZZ_TOTAL_RUNS + RUNS))
    ELAPSED=$((i * SEGMENT))

    find "$FUZZ_DIR/profraw" -name "*.profraw" | xargs "$LLVM_PROFDATA" merge -sparse -o "$FUZZ_DIR/merged.profdata" 2>/dev/null

    # Count corpus size as proxy for "valid inputs that found new coverage"
    CORPUS_SIZE=$(find "$FUZZ_DIR/corpus" -type f | wc -l)

    SUMMARY=$(coverage_json "$FUZZ_BIN" "$FUZZ_DIR/merged.profdata" "$ELAPSED" "$FUZZ_TOTAL_RUNS" "$CORPUS_SIZE")

    if [ "$FIRST" = true ]; then FIRST=false; else echo "," >> "$FUZZ_DIR/coverage_over_time.json"; fi
    echo "  $SUMMARY" >> "$FUZZ_DIR/coverage_over_time.json"
    echo "  ${ELAPSED}s | ${FUZZ_TOTAL_RUNS} attempts | corpus=${CORPUS_SIZE} | $(echo "$SUMMARY" | python3 -c "import json,sys;d=json.load(sys.stdin);print(f\"tc={d['typechecker_pct']}% val={d['validator_pct']}%\")")"
done

echo "]" >> "$FUZZ_DIR/coverage_over_time.json"

# =========== GENERATOR ===========
echo ""
echo "========== GENERATOR ($GENERATOR, ${DURATION}s, ${SEGMENT}s segments) =========="

GEN_DIR="$OUTPUT_DIR/$GENERATOR"
mkdir -p "$GEN_DIR/profraw"

echo "[" > "$GEN_DIR/coverage_over_time.json"
FIRST=true
GEN_SEED=0
GEN_TOTAL_ATTEMPTS=0
GEN_TOTAL_VALID=0

for i in $(seq 1 $NUM_SEGMENTS); do
    # Run generator for SEGMENT seconds
    OUTPUT=$(LLVM_PROFILE_FILE="$GEN_DIR/profraw/seg${i}_%m.profraw" \
        "$GEN_BIN" \
        --generator "$GENERATOR" \
        --duration "$SEGMENT" \
        --seed "$GEN_SEED" \
        --buffer-size "$BUFFER_SIZE" \
        --report-interval 999999999 2>&1)

    # Parse "Done. NNN valid inputs from MMM attempts in X.XXs"
    ATTEMPTS=$(echo "$OUTPUT" | grep -oP '\d+(?= attempts in)' | tail -1)
    ATTEMPTS=${ATTEMPTS:-0}
    VALID=$(echo "$OUTPUT" | grep -oP '\d+(?= valid inputs)' | tail -1)
    VALID=${VALID:-0}

    GEN_TOTAL_ATTEMPTS=$((GEN_TOTAL_ATTEMPTS + ATTEMPTS))
    GEN_TOTAL_VALID=$((GEN_TOTAL_VALID + VALID))
    GEN_SEED=$((GEN_SEED + ATTEMPTS))
    ELAPSED=$((i * SEGMENT))

    find "$GEN_DIR/profraw" -name "*.profraw" | xargs "$LLVM_PROFDATA" merge -sparse -o "$GEN_DIR/merged.profdata" 2>/dev/null

    SUMMARY=$(coverage_json "$GEN_BIN" "$GEN_DIR/merged.profdata" "$ELAPSED" "$GEN_TOTAL_ATTEMPTS" "$GEN_TOTAL_VALID")

    if [ "$FIRST" = true ]; then FIRST=false; else echo "," >> "$GEN_DIR/coverage_over_time.json"; fi
    echo "  $SUMMARY" >> "$GEN_DIR/coverage_over_time.json"
    echo "  ${ELAPSED}s | ${GEN_TOTAL_ATTEMPTS} attempts | ${GEN_TOTAL_VALID} valid | $(echo "$SUMMARY" | python3 -c "import json,sys;d=json.load(sys.stdin);print(f\"tc={d['typechecker_pct']}% val={d['validator_pct']}%\")")"
done

echo "]" >> "$GEN_DIR/coverage_over_time.json"

# =========== SUMMARY TABLE ===========
echo ""
echo "========== COMPARISON (time-based) =========="
python3 -c "
import json
fuzz = json.load(open('$FUZZ_DIR/coverage_over_time.json'))
gen = json.load(open('$GEN_DIR/coverage_over_time.json'))
print(f\"{'Time':>6} | {'Fuzzer':>30} | {'Generator':>30}\")
print(f\"{'':>6} | {'attempts   valid   TC%':>30} | {'attempts   valid   TC%':>30}\")
print('-' * 72)
for i in range(max(len(fuzz), len(gen))):
    t = fuzz[i]['elapsed_secs'] if i < len(fuzz) else gen[i]['elapsed_secs']
    if i < len(fuzz):
        f = f\"{fuzz[i]['attempts']:>8}  {fuzz[i]['valid_inputs']:>6}  {fuzz[i]['typechecker_pct']:>6}%\"
    else:
        f = '-'
    if i < len(gen):
        g = f\"{gen[i]['attempts']:>8}  {gen[i]['valid_inputs']:>6}  {gen[i]['typechecker_pct']:>6}%\"
    else:
        g = '-'
    print(f'{t:>5}s | {f:>30} | {g:>30}')
"
