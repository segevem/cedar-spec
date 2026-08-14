#!/bin/bash
#
# RUSTC_WRAPPER that adds `-C instrument-coverage` ONLY for the cedar-policy crates whose
# LINE coverage we measure (cedar_policy + cedar_policy_core) — plus the cedar_drt_coverage
# bin itself, purely to guarantee the LLVM profiling runtime (__llvm_profile_*) links.
#
# Everything else — cedar-policy-generators, cedar-lean-ffi, cedar-drt, symcc, and all
# third-party deps — is compiled WITHOUT instrumentation. Result:
#   * the LLVM counter array holds ONLY cedar-policy(+core) counters (small) -> cheap to
#     read/dump, and no memory-bandwidth blowup;
#   * instrument-coverage RUNTIME overhead (per-region counter bumps) is confined to the
#     code under test — the generators/FFI/harness run at full native speed.
# These are exactly the crates the coverage_analyze.py IGNORE_REGEX keeps, so nothing we
# report is lost.
#
# The instrumented crate set is overridable via $INSTRUMENT_CRATES (space-separated crate
# names). Default = the validator crates (cedar_policy + cedar_policy_core). For the SymCC
# experiment we instrument the symbolic COMPILER instead — the target measures compiler
# coverage, not the validator — via INSTRUMENT_CRATES="cedar_policy_symcc cedar_drt_coverage".
# cedar_drt_coverage must always be included so the LLVM profiling runtime (__llvm_profile_*)
# links into the binary.
#
# Usage:  RUSTC_WRAPPER=/abs/path/instrument_cedar_only.sh cargo build ... (do NOT also set
#         RUSTFLAGS="-C instrument-coverage", which would instrument everything).
INSTRUMENT_CRATES="${INSTRUMENT_CRATES:-cedar_policy cedar_policy_core cedar_drt_coverage}"
rustc="$1"; shift
crate=""
prev=""
for a in "$@"; do
  [[ "$prev" == "--crate-name" ]] && crate="$a"
  prev="$a"
done
for want in $INSTRUMENT_CRATES; do
  if [[ "$crate" == "$want" ]]; then
    exec "$rustc" "$@" -C instrument-coverage
  fi
done
exec "$rustc" "$@"
