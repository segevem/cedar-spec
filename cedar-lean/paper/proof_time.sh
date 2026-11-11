#!/usr/bin/env bash
# The time the expression generator's derivation and its proofs take from cold: a warm build first,
# then `CedarGen/Relational/ExprGen.lean` touched (a definition appended, removed afterwards), so that
# it and every proof file is rebuilt, and that rebuild timed. Also prints the audit's law counts.
#
#   paper/proof_time.sh [runs]        # from cedar-lean, after ./build_native_libs.sh
set -euo pipefail
cd "$(dirname "$0")/.."
runs=${1:-2}
log=$(mktemp -d)
lake env lake -R build CedarGenProof > "$log/warm.log" 2>&1
cp CedarGen/Relational/ExprGen.lean "$log/ExprGen.lean"
trap 'cp "$log/ExprGen.lean" CedarGen/Relational/ExprGen.lean' EXIT
for i in $(seq "$runs"); do
  printf "\ndef timingNonce%s : Nat := 0\n" "$(date +%s%N)" >> CedarGen/Relational/ExprGen.lean
  s=$(date +%s.%N)
  lake env lake build CedarGenProof > "$log/run$i.log" 2>&1
  e=$(date +%s.%N)
  cp "$log/ExprGen.lean" CedarGen/Relational/ExprGen.lean
  eg=$(grep -oE 'Built CedarGen.Relational.ExprGen \([0-9.]+s\)' "$log/run$i.log" | grep -oE '[0-9.]+s' || true)
  laws=$(grep -oE 'laws checked: [0-9]+; with nonstandard axioms: [0-9]+' "$log/run$i.log" | tail -1)
  python3 -c "print('run $i: derivation and proofs %.0f s (ExprGen module ${eg:-?}) | $laws' % ($e - $s))"
done
echo "logs: $log"
