#!/usr/bin/env python3
"""The inductive relations of the relational specification of Cedar's validator
(`Cedar/Validation/Relational`), counted from the sources.

  python3 paper/count_relations.py
"""
import pathlib, re
root = pathlib.Path(__file__).resolve().parent.parent / "Cedar" / "Validation" / "Relational"
pat = re.compile(r"^\s*(?:private\s+)?inductive\s+(\S+)", re.M)
total = 0
for f in sorted(root.glob("*.lean")):
    n = len(pat.findall(f.read_text()))
    total += n
    print(f"{f.name:<20} {n}")
print(f"{'total':<20} {total}")
