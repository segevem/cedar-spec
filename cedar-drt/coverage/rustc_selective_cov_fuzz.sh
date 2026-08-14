#!/bin/bash
# RUSTC_WRAPPER for the fuzzer: adds -C instrument-coverage only to cedar-policy crates.
# sancov flags are already passed via RUSTFLAGS by cargo-fuzz.

CRATE_NAME=""
prev=""
for arg in "$@"; do
    if [ "$prev" = "--crate-name" ]; then
        CRATE_NAME="$arg"
        break
    fi
    prev="$arg"
done

case "$CRATE_NAME" in
    cedar_policy_core|cedar_policy|cedar_drt_inner)
        exec "$@" -C instrument-coverage
        ;;
    *)
        exec "$@"
        ;;
esac
