#!/bin/bash
# RUSTC_WRAPPER that only adds sancov flags for cedar-policy-core and cedar-policy crates.
# Used to build the fuzzer binary so libfuzzer only gets feedback from the validator,
# not from the generators.
#
# Usage: RUSTC_WRAPPER=./rustc_selective_sancov_fuzz.sh cargo build --release --bin validation-drt-type-directed

CRATE_NAME=""
for arg in "$@"; do
    if [ "$prev" = "--crate-name" ]; then
        CRATE_NAME="$arg"
        break
    fi
    prev="$arg"
done

SANCOV_FLAGS="-Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-level=4 -Cllvm-args=-sanitizer-coverage-inline-8bit-counters -Cllvm-args=-sanitizer-coverage-pc-table -Cllvm-args=-sanitizer-coverage-trace-compares"

case "$CRATE_NAME" in
    cedar_policy_core|cedar_policy)
        exec "$@" $SANCOV_FLAGS
        ;;
    *)
        exec "$@"
        ;;
esac
