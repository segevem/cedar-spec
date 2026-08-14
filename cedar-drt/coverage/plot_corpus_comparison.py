#!/usr/bin/env python3
"""Plot typechecker coverage growth vs corpus size, with throughput annotation."""

import json
import sys
import matplotlib.pyplot as plt

if len(sys.argv) < 3:
    print("Usage: plot_corpus_comparison.py <specimen.json> <fuzz.json> [output.png]")
    sys.exit(1)

specimen_path = sys.argv[1]
fuzz_path = sys.argv[2]
output_path = sys.argv[3] if len(sys.argv) > 3 else "corpus_coverage.png"

with open(specimen_path) as f:
    specimen_data = json.load(f)
with open(fuzz_path) as f:
    fuzz_data = json.load(f)

fig, ax = plt.subplots(figsize=(10, 6))

# Specimen
spec_x = [d["corpus_idx"] for d in specimen_data]
spec_y = [d["typechecker_pct"] for d in specimen_data]
ax.plot(spec_x, spec_y, "s-", color="tab:blue", linewidth=2, markersize=4,
        label=f"Specimen-Derived Unguided ({spec_x[-1]} corpus entries)")

# Fuzzer
fuzz_x = [d["corpus_idx"] for d in fuzz_data]
fuzz_y = [d["typechecker_pct"] for d in fuzz_data]
ax.plot(fuzz_x, fuzz_y, "o-", color="tab:red", linewidth=2, markersize=4,
        label=f"Handwritten Guided ({fuzz_x[-1]} corpus entries)")

ax.set_xlabel("Corpus Size (# coverage-expanding inputs)", fontsize=12)
ax.set_ylabel("Typechecker Coverage (%)", fontsize=12)
ax.set_title("Typechecker Coverage vs Corpus Size\n(Replayed through same -C instrument-coverage binary)", fontsize=13)
ax.legend(fontsize=11)
ax.grid(True, alpha=0.3)
ax.set_ylim(0, 100)

info_text = (
    f"Specimen: {spec_x[-1]} inputs → {spec_y[-1]}%\n"
    f"Fuzzer: {fuzz_x[-1]} inputs → {fuzz_y[-1]}%"
)
ax.text(0.02, 0.98, info_text, transform=ax.transAxes, fontsize=9,
        verticalalignment="top", fontfamily="monospace",
        bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.5))

plt.tight_layout()
plt.savefig(output_path, dpi=150)
print(f"Graph saved to: {output_path}")
