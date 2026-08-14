#!/bin/bash
# Clean corpus-based comparison:
# 1. Generate Specimen corpus (sancov build, EdgeTracker filters novel inputs)
# 2. Generate Fuzzer corpus (cargo-fuzz sancov build, libfuzzer filters novel inputs)
# 3. Replay both through same -C instrument-coverage binary
# 4. Measure source coverage with llvm-cov at each corpus entry
# 5. Plot coverage growth vs corpus index
#
# Usage:
#   bash run_corpus_comparison.sh [DURATION]
#   bash run_corpus_comparison.sh 90

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DURATION=${1:-90}

FUZZ_BIN="$SCRIPT_DIR/../fuzz/target/x86_64-unknown-linux-gnu/release/validation-drt-type-directed"
LEAN_LIB=/local/home/segevem/.elan/toolchains/leanprover--lean4---v4.30.0-rc1/lib/lean
LLVM_PROFDATA=$(find "$(rustc --print sysroot)" -name llvm-profdata 2>/dev/null | head -1)
LLVM_COV=$(find "$(rustc --print sysroot)" -name llvm-cov 2>/dev/null | head -1)

OUTPUT_DIR="$SCRIPT_DIR/corpus_comparison"
rm -rf "$OUTPUT_DIR"
mkdir -p "$OUTPUT_DIR"

# === Step 1: Build sancov binary for corpus generation ===
echo "=== Building sancov binary (for corpus generation) ==="
CARGO_TARGET_DIR="$SCRIPT_DIR/target_sancov" RUSTC_WRAPPER="$SCRIPT_DIR/rustc_sancov.sh" cargo build --release --features lean-gen 2>&1 | tail -1
SANCOV_BIN="$SCRIPT_DIR/target_sancov/release/cedar-drt-coverage"

# === Step 2: Generate Specimen corpus ===
echo ""
echo "=== Generating Specimen corpus (${DURATION}s) ==="
SPECIMEN_CORPUS="$OUTPUT_DIR/specimen_corpus"
"$SANCOV_BIN" \
    --generator lean-schema-typeof \
    --duration "$DURATION" \
    --report-interval 10000 \
    --corpus-dir "$SPECIMEN_CORPUS" 2>&1 | grep -E "Done\.|Novel|Throughput"
echo "  Corpus size: $(ls "$SPECIMEN_CORPUS" | wc -l) inputs"

# === Step 3: Generate Fuzzer corpus ===
echo ""
echo "=== Running cargo-fuzz type-directed (${DURATION}s, validator-only sancov) ==="
FUZZ_CORPUS="$OUTPUT_DIR/fuzz_corpus"
mkdir -p "$FUZZ_CORPUS"
LD_LIBRARY_PATH="$LEAN_LIB" "$FUZZ_BIN" "$FUZZ_CORPUS" -max_total_time="$DURATION" 2>&1 | tail -2
echo "  Corpus size: $(ls "$FUZZ_CORPUS" | wc -l) inputs"

# === Step 4: Build replay binary with -C instrument-coverage ===
echo ""
echo "=== Building replay binary (-C instrument-coverage, validator only) ==="
CARGO_TARGET_DIR="$SCRIPT_DIR/target_cov" RUSTC_WRAPPER="$SCRIPT_DIR/rustc_selective_cov.sh" cargo build --release --features lean-gen 2>&1 | tail -1
REPLAY_BIN="$SCRIPT_DIR/target_cov/release/cedar-drt-coverage"

# === Step 5: Replay Specimen corpus incrementally ===
echo ""
echo "=== Replaying Specimen corpus ==="
SPECIMEN_PROFDIR="$OUTPUT_DIR/specimen_profraw"
mkdir -p "$SPECIMEN_PROFDIR"

SPECIMEN_FILES=($(ls "$SPECIMEN_CORPUS" | sort))
SPECIMEN_TOTAL=${#SPECIMEN_FILES[@]}
BATCH=$((SPECIMEN_TOTAL / 20 + 1))  # ~20 data points

echo "[" > "$OUTPUT_DIR/specimen_coverage.json"
FIRST=true
for i in $(seq $BATCH $BATCH $SPECIMEN_TOTAL) $SPECIMEN_TOTAL; do
    [ "$i" -gt "$SPECIMEN_TOTAL" ] && continue
    # Replay first i entries
    rm -f "$SPECIMEN_PROFDIR"/*.profraw
    HEAD_FILES=$(ls "$SPECIMEN_CORPUS" | sort | head -"$i")
    # Create temp dir with just the first i files
    TMPDIR=$(mktemp -d)
    for f in $HEAD_FILES; do ln -s "$SPECIMEN_CORPUS/$f" "$TMPDIR/$f"; done
    LLVM_PROFILE_FILE="$SPECIMEN_PROFDIR/%m.profraw" "$REPLAY_BIN" --replay-proto "$TMPDIR" 2>/dev/null
    rm -rf "$TMPDIR"

    "$LLVM_PROFDATA" merge -sparse "$SPECIMEN_PROFDIR"/*.profraw -o "$SPECIMEN_PROFDIR/merged.profdata" 2>/dev/null
    TC_PCT=$("$LLVM_COV" export "$REPLAY_BIN" \
        -instr-profile="$SPECIMEN_PROFDIR/merged.profdata" \
        -format=text --ignore-filename-regex='/.cargo/registry|/rustc/' \
        -summary-only 2>/dev/null | python3 -c "
import json,sys;data=json.load(sys.stdin)
tc_cov=tc_tot=0
for f in data['data'][0]['files']:
    lines=f['summary']['lines'];name=f['filename']
    if '/validator' in name:
        bn=name.split('/')[-1]
        if any(k in bn for k in ['typecheck','rbac','expr_iterator','partition','diagnostics','extension']):
            tc_cov+=lines['covered'];tc_tot+=lines['count']
print(round(100.0*tc_cov/tc_tot,2) if tc_tot>0 else 0)
")
    if [ "$FIRST" = true ]; then FIRST=false; else echo "," >> "$OUTPUT_DIR/specimen_coverage.json"; fi
    echo "  {\"corpus_idx\": $i, \"typechecker_pct\": $TC_PCT}" >> "$OUTPUT_DIR/specimen_coverage.json"
    echo "  $i/$SPECIMEN_TOTAL: TC=$TC_PCT%"
done
echo "]" >> "$OUTPUT_DIR/specimen_coverage.json"

# === Step 6: Replay Fuzzer corpus incrementally ===
echo ""
echo "=== Replaying Fuzzer corpus ==="
FUZZ_PROFDIR="$OUTPUT_DIR/fuzz_profraw"
mkdir -p "$FUZZ_PROFDIR"

FUZZ_FILES=($(ls "$FUZZ_CORPUS" | sort))
FUZZ_TOTAL=${#FUZZ_FILES[@]}
BATCH=$((FUZZ_TOTAL / 20 + 1))

echo "[" > "$OUTPUT_DIR/fuzz_coverage.json"
FIRST=true
for i in $(seq $BATCH $BATCH $FUZZ_TOTAL) $FUZZ_TOTAL; do
    [ "$i" -gt "$FUZZ_TOTAL" ] && continue
    rm -f "$FUZZ_PROFDIR"/*.profraw
    HEAD_FILES=$(ls "$FUZZ_CORPUS" | sort | head -"$i")
    TMPDIR=$(mktemp -d)
    for f in $HEAD_FILES; do ln -s "$FUZZ_CORPUS/$f" "$TMPDIR/$f"; done
    LLVM_PROFILE_FILE="$FUZZ_PROFDIR/%m.profraw" "$REPLAY_BIN" --replay-fuzz "$TMPDIR" 2>/dev/null
    rm -rf "$TMPDIR"

    "$LLVM_PROFDATA" merge -sparse "$FUZZ_PROFDIR"/*.profraw -o "$FUZZ_PROFDIR/merged.profdata" 2>/dev/null
    TC_PCT=$("$LLVM_COV" export "$REPLAY_BIN" \
        -instr-profile="$FUZZ_PROFDIR/merged.profdata" \
        -format=text --ignore-filename-regex='/.cargo/registry|/rustc/' \
        -summary-only 2>/dev/null | python3 -c "
import json,sys;data=json.load(sys.stdin)
tc_cov=tc_tot=0
for f in data['data'][0]['files']:
    lines=f['summary']['lines'];name=f['filename']
    if '/validator' in name:
        bn=name.split('/')[-1]
        if any(k in bn for k in ['typecheck','rbac','expr_iterator','partition','diagnostics','extension']):
            tc_cov+=lines['covered'];tc_tot+=lines['count']
print(round(100.0*tc_cov/tc_tot,2) if tc_tot>0 else 0)
")
    if [ "$FIRST" = true ]; then FIRST=false; else echo "," >> "$OUTPUT_DIR/fuzz_coverage.json"; fi
    echo "  {\"corpus_idx\": $i, \"typechecker_pct\": $TC_PCT}" >> "$OUTPUT_DIR/fuzz_coverage.json"
    echo "  $i/$FUZZ_TOTAL: TC=$TC_PCT%"
done
echo "]" >> "$OUTPUT_DIR/fuzz_coverage.json"

# === Step 7: Plot ===
echo ""
echo "=== Plotting ==="
python3 "$SCRIPT_DIR/plot_corpus_comparison.py" \
    "$OUTPUT_DIR/specimen_coverage.json" \
    "$OUTPUT_DIR/fuzz_coverage.json" \
    "$OUTPUT_DIR/corpus_coverage.png"
