#!/bin/bash
# RUSTC_WRAPPER that only adds -C instrument-coverage for cedar-policy-core and cedar-policy crates.
# Usage: RUSTC_WRAPPER=./rustc_selective_cov.sh cargo build --release

CRATE_NAME=""
for arg in "$@"; do
    if [ "$prev" = "--crate-name" ]; then
        CRATE_NAME="$arg"
        break
    fi
    prev="$arg"
done

# Instrument cedar-policy crates + the top-level binary
# The top-level binary needs instrument-coverage to link the profiling runtime
case "$CRATE_NAME" in
    cedar_policy_core|cedar_policy|cedar_drt_coverage)
        exec "$@" -C instrument-coverage
        ;;
    *)
        exec "$@"
        ;;
esac
