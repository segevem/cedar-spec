#!/usr/bin/env bash
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

# The table of derived definitions: the generators' modules rebuilt with Specimen writing out what it
# derives (`SPECIMEN_DUMP_CODE`), then tabulated (`derived_table.py`).
#
#   paper/derived_table.sh [dir]      # from cedar-lean
set -euo pipefail
cd "$(dirname "$0")/.."
dir=${1:-/tmp/cedar-dump}
rm -rf "$dir"
mods=(CedarGen/Relational/ExprGen.lean CedarGen/Relational/PolicyGen.lean CedarGen/Relational/SchemaGen.lean)
for f in "${mods[@]}"; do cp "$f" "$f.orig"; printf "\ndef dumpNonce%s : Nat := 0\n" "$(date +%s%N)" >> "$f"; done
trap 'for f in "${mods[@]}"; do mv "$f.orig" "$f"; done' EXIT
SPECIMEN_DUMP_CODE="$dir" lake env lake -R build CedarGen.Relational.ExprGen CedarGen.Relational.PolicyGen \
  CedarGen.Relational.SchemaGen > "$dir.log" 2>&1
python3 paper/derived_table.py "$dir"
