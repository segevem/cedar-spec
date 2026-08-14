#!/bin/bash
set -euo pipefail
cd /local/home/segevem/cedar-spec/cedar-drt/coverage

export LD_LIBRARY_PATH=/local/home/segevem/.elan/toolchains/leanprover--lean4---v4.30.0-rc1/lib/lean
export LLVM_PROFILE_FILE=coverage_results/fuzzer/profraw/fuzz_%m.profraw

/local/home/segevem/cedar-spec/cedar-drt/fuzz/target/x86_64-unknown-linux-gnu/release/validation-drt \
    coverage_results/fuzzer/corpus \
    -max_total_time=10 2>&1 | tail -3

echo "---"
ls coverage_results/fuzzer/profraw/ | wc -l
