#!/usr/bin/env bash
# Generator speed, Basalt against Plausible, for the production expression derivation without its
# proofs: how long the derivation takes with each emission (the `GenSpeed*.Derive` modules, rebuilt
# from cold), then how fast each derived generator runs, alternating, `reps` times. `GenSpeedOn io`
# runs the Basalt generator at `IO`, with Basalt's SplitMix; `GenSpeedOn` through the bridge to
# Plausible's `StdGen`; `GenSpeedOff` is the generator emitted against Plausible.
#
#   paper/gen_speed.sh [reps] [terms per type] [size]     # from cedar-lean
set -euo pipefail
cd "$(dirname "$0")/.."
reps=${1:-4}; n=${2:-300}; size=${3:-8}
log=$(mktemp -d)
lake env lake -R build CedarGen > "$log/deps.log" 2>&1
# A definition appended to each derivation forces it to be rebuilt (Lake compares contents, not times).
cp GenSpeedOn/Derive.lean "$log/DeriveOn.lean"; cp GenSpeedOff/Derive.lean "$log/DeriveOff.lean"
trap 'cp "$log/DeriveOn.lean" GenSpeedOn/Derive.lean; cp "$log/DeriveOff.lean" GenSpeedOff/Derive.lean' EXIT
for m in On Off; do
  printf "\ndef timingNonce%s : Nat := 0\n" "$(date +%s%N)" >> GenSpeed$m/Derive.lean
  lake env lake build GenSpeed$m.Derive > "$log/derive$m.log" 2>&1
  cp "$log/Derive$m.lean" GenSpeed$m/Derive.lean
  echo "derivation, emission ${m,,}: $(grep -oE "Built GenSpeed$m.Derive \([0-9.]+s\)" "$log/derive$m.log" | grep -oE '[0-9.]+s')"
done
lake env lake build GenSpeedOn GenSpeedOff > "$log/exes.log" 2>&1
for r in $(seq "$reps"); do
  echo "rep $r"
  echo "  Basalt, SplitMix:      $(lake env .lake/build/bin/GenSpeedOn "$n" "$size" io)"
  echo "  Basalt, Plausible RNG: $(lake env .lake/build/bin/GenSpeedOn "$n" "$size")"
  echo "  Plausible:             $(lake env .lake/build/bin/GenSpeedOff "$n" "$size")"
done
echo "logs: $log"
