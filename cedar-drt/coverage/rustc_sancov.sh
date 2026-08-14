#!/bin/bash
# RUSTC_WRAPPER that adds sancov inline-8bit-counters for cedar-policy crates only.
# This enables in-process edge tracking (EdgeTracker) without libfuzzer.
# Usage: RUSTC_WRAPPER=./rustc_sancov.sh cargo build --release

CRATE_NAME=""
for arg in "$@"; do
    if [ "$prev" = "--crate-name" ]; then
        CRATE_NAME="$arg"
        break
    fi
    prev="$arg"
done

case "$CRATE_NAME" in
    cedar_policy_core|cedar_policy)
        exec "$@" \
            -Cpasses=sancov-module \
            -Cllvm-args=-sanitizer-coverage-level=3 \
            -Cllvm-args=-sanitizer-coverage-inline-8bit-counters
        ;;
    cedar_drt_coverage)
        exec "$@"
        ;;
    *)
        exec "$@"
        ;;
esac
