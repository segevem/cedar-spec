#!/usr/bin/env python3
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

"""The table of derived definitions (tab:cedar-derived): definitions, lines of derived code and mutually
recursive groups, by sort, for the expression, policy and schema generators.

Reads the `components.jsonl` that `SPECIMEN_DUMP_CODE=<dir>` has Specimen write while the generators'
modules build (one line per derived component: its module and members, each with its sort and line
counts); `paper/derived_table.sh` runs that build.

  python3 paper/derived_table.py <dir>
"""
import json, sys
from collections import defaultdict

AREAS = {"CedarGen.Relational.ExprGen": "Expressions", "CedarGen.Relational.PolicyGen": "Policies",
         "CedarGen.Relational.SchemaGen": "Schemas"}

def area(module):
    return AREAS.get(module)

SORTS = ["Generator", "Enumerator", "Checker"]

def sort_of(s):
    for k in SORTS:
        if s.endswith(k): return k
    raise ValueError(s)

def main(d):
    defs = defaultdict(lambda: defaultdict(int))
    lines = defaultdict(lambda: defaultdict(int))
    groups = defaultdict(list)
    seen = set()
    for line in open(f"{d}/components.jsonl"):
        c = json.loads(line)
        a = area(c["module"])
        if a is None: continue
        members = [m for m in c["members"] if (c["module"], m["name"]) not in seen]
        if not members: continue
        for m in members:
            seen.add((c["module"], m["name"]))
            k = sort_of(m["sort"])
            defs[a][k] += 1
            lines[a][k] += m["defLines"]
        groups[a].append(len(members))
    rows = ["Expressions", "Policies", "Schemas"]
    def row(name, ds, ls, gs):
        big = [g for g in gs if g > 1]
        mean = sum(gs) / len(gs) if gs else 0
        meanbig = f"{sum(big) / len(big):.2f}" if big else "---"
        cells = [ds[k] for k in SORTS] + [f"{ls[k]:,}" for k in SORTS] + \
                [len(gs), max(gs) if gs else 0, f"{mean:.2f}", meanbig]
        print(f"{name:<12}" + " & ".join(f"{x:>7}" for x in cells) + r" \\")
    print(f"{'':<12}" + " & ".join(f"{h:>7}" for h in
          ["Gen.", "Enum.", "Check.", "Gen.", "Enum.", "Check.", "Groups", "Largest", "Mean", "Mean>1"]))
    tot_d, tot_l, tot_g = defaultdict(int), defaultdict(int), []
    for a in rows:
        row(a, defs[a], lines[a], groups[a])
        for k in SORTS: tot_d[k] += defs[a][k]; tot_l[k] += lines[a][k]
        tot_g += groups[a]
    row("Total", tot_d, tot_l, tot_g)
    n = sum(tot_d.values()); loc = sum(tot_l.values())
    print(f"\n{n} definitions, {loc:,} lines, {sum(1 for g in tot_g if g > 1)} mutually recursive groups")

if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "/tmp/cedar-dump")
