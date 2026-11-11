#!/bin/bash
# Copyright Cedar Contributors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# The Lean side of the `specimen-gen` feature: build `CedarFFIGen` (the FFI and the derived
# generators), then compile every module it reaches (Cedar, Specimen, Basalt, Mathlib's part, ...)
# and pack them into one archive, `libCedarFFIGen_all.a`, which the feature links.
set -euo pipefail
cd "$(dirname "$0")/../cedar-lean"
lake build CedarFFIGen
mods=$(lake env lean --run scripts/ListMods.lean CedarFFIGen | grep -v -E '^(Init|Std|Lean|Lake)(\.|$)')
dirs=("$(pwd)")
for d in .lake/packages/*; do dirs+=("$(pwd)/$d"); done
obj=.lake/build/ffi-gen
mkdir -p "$obj"
: > "$obj/jobs.txt"
for m in $mods; do
  rel="${m//.//}.c"
  c=""
  for d in "${dirs[@]}"; do
    if [ -f "$d/.lake/build/ir/$rel" ]; then c="$d/.lake/build/ir/$rel"; break; fi
  done
  if [ -z "$c" ]; then echo "no C file for $m" >&2; exit 1; fi
  echo "$c $obj/$m.o" >> "$obj/jobs.txt"
done
leanc=$(dirname "$(command -v lean)")/leanc
# Compile only what changed.
xargs -P "$(nproc)" -L 1 bash -c \
  'if [ ! -f "$1" ] || [ "$0" -nt "$1" ]; then '"$leanc"' -c -O3 -DNDEBUG -fPIC -o "$1" "$0"; fi' < "$obj/jobs.txt"
rm -f .lake/build/lib/libCedarFFIGen_all.a
awk '{print $2}' "$obj/jobs.txt" | xargs ar rcs .lake/build/lib/libCedarFFIGen_all.a
# SplitMix's C implementation, which Basalt's `IO` generators call.
(cd "$obj" && ar x ../../packages/splitmix/.lake/build/lib/libsplitmix.a)
ar rs .lake/build/lib/libCedarFFIGen_all.a "$obj"/splitmix*.o
echo "libCedarFFIGen_all.a: $(wc -l < "$obj/jobs.txt") modules"
