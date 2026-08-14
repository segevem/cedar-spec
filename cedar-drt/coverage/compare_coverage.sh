#!/bin/bash
# Compare coverage over time between two generators.
#
# Usage:
#   ./compare_coverage.sh [OPTIONS]
#
# Runs both generators with the same iteration/batch parameters and
# produces a combined JSON file and a terminal summary.
#
# Requires: cargo-llvm-cov, python3

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

GENERATORS=("type-directed" "undirected")
ITERATIONS=100000
SEED=0
BATCH_SIZE=10000
BUFFER_SIZE=65536
OUTPUT_DIR="./coverage_results"

while [[ $# -gt 0 ]]; do
    case $1 in
        --generators) IFS=',' read -ra GENERATORS <<< "$2"; shift 2 ;;
        --iterations) ITERATIONS="$2"; shift 2 ;;
        --seed) SEED="$2"; shift 2 ;;
        --batch-size) BATCH_SIZE="$2"; shift 2 ;;
        --buffer-size) BUFFER_SIZE="$2"; shift 2 ;;
        --output-dir) OUTPUT_DIR="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

echo "=== Comparing generators: ${GENERATORS[*]} ==="
echo "    iterations=$ITERATIONS, batch=$BATCH_SIZE"
echo ""

for gen in "${GENERATORS[@]}"; do
    echo "--- Running: $gen ---"
    "$SCRIPT_DIR/run_coverage.sh" \
        --generator "$gen" \
        --iterations "$ITERATIONS" \
        --seed "$SEED" \
        --batch-size "$BATCH_SIZE" \
        --buffer-size "$BUFFER_SIZE" \
        --output-dir "$OUTPUT_DIR"
    echo ""
done

# Produce comparison summary
echo "=== Comparison Summary ==="
python3 -c "
import json, sys, os

output_dir = '$OUTPUT_DIR'
generators = '${GENERATORS[*]}'.split()

print(f\"{'Iterations':>12} | \", end='')
for g in generators:
    print(f'{g:>25} | ', end='')
print()
print('-' * (14 + 28 * len(generators)))

# Load all data
all_data = {}
for g in generators:
    path = os.path.join(output_dir, g, 'coverage_over_time.json')
    with open(path) as f:
        all_data[g] = json.load(f)

# Print rows at each batch point
max_rows = max(len(v) for v in all_data.values())
for i in range(max_rows):
    iters = all_data[generators[0]][i]['iterations'] if i < len(all_data[generators[0]]) else '?'
    print(f'{iters:>12} | ', end='')
    for g in generators:
        if i < len(all_data[g]):
            d = all_data[g][i]
            print(f\"{d['lines_covered']}/{d['lines_total']} ({d['line_coverage_pct']}%)\".rjust(25) + ' | ', end='')
        else:
            print(' ' * 25 + ' | ', end='')
    print()
"
