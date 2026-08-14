#!/usr/bin/env python3
"""Visualize the cross-approach line-coverage overlap/diff from coverage_compare.json.

No specimen-vs-handwritten assumption: every label uses the REAL approach names
parsed from each `<left>_vs_<right>` pair key (so a handwritten-vs-handwritten pair,
e.g. `hw-slots-off_vs_hw-slots-on`, is labelled correctly rather than mislabelled
"specimen"/"handwritten"). Layout:
  * Top (full width): per-pair overlap — a stacked bar of only-left | shared |
    only-right region-lines per pair, Jaccard annotated; each row's ytick names the
    two approaches, and the legend is generic (left / shared / right).
  * Below: one by-function panel PER pair — the top-N functions by disagreement, as
    grouped bars (only-left vs only-right), titled and legended with that pair's two
    approach names.

Reads <root>/coverage_compare.json, writes <root>/coverage_compare.png.
"""
import argparse
import json
import math
import os
import shutil
import subprocess

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from matplotlib.patches import Patch
import numpy as np

C_SHARED, C_A, C_B = "#8c9bab", "#2b7bba", "#d1743c"  # shared, left-only, right-only


def demangle_all(symbols):
    """Demangle raw Rust symbols via `rustfilt` (rustc-demangle) in ONE batch call —
    correct for v0/legacy mangling (crate hashes, `Nt`, backrefs). Falls back to the raw
    symbol if rustfilt is unavailable. Returns {raw: demangled}."""
    uniq = list(dict.fromkeys(symbols))
    rf = shutil.which("rustfilt")
    if not rf or not uniq:
        return {s: s for s in uniq}
    try:
        out = subprocess.run([rf], input="\n".join(uniq), capture_output=True,
                             text=True, check=True).stdout.splitlines()
        if len(out) == len(uniq):
            return dict(zip(uniq, out))
    except (subprocess.CalledProcessError, OSError):
        pass
    return {s: s for s in uniq}


def short_fn(demangled):
    """Trailing path components of a demangled name, trimmed for the axis label."""
    return "::".join(demangled.split("::")[-2:])[:48]


def split_pair(name):
    """`<left>_vs_<right>` -> (left, right). only_a is the left approach's unique lines,
    only_b the right's. `<x>_vs_handwritten` pairs compare against the guided union."""
    if "_vs_" in name:
        left, right = name.split("_vs_", 1)
        return left, right
    return name, "other"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--out", default=None)
    ap.add_argument("--top", type=int, default=15)
    args = ap.parse_args()

    path = os.path.join(args.root, "coverage_compare.json")
    if not os.path.exists(path):
        print(f"no {path}; skipping"); return
    with open(path) as f:
        doc = json.load(f)
    pairs = doc.get("pairs", {})
    if not pairs:
        print("no pairs in coverage_compare.json; skipping"); return

    names = list(pairs.keys())
    P = len(names)

    # Demangle every symbol we'll plot (top-N of each pair) in one rustfilt batch.
    all_syms = [d["fn"] for n in names for d in pairs[n].get("by_function", [])[: args.top]]
    dm = demangle_all(all_syms)

    ncols = 2 if P > 1 else 1
    nrows_fn = math.ceil(P / ncols)
    fig = plt.figure(figsize=(9 * ncols, 3.4 + 3.2 * nrows_fn))
    gs = gridspec.GridSpec(1 + nrows_fn, ncols, figure=fig,
                           height_ratios=[1.5] + [1.0] * nrows_fn,
                           hspace=0.55, wspace=0.4)

    # --- Top panel (full width): per-pair set breakdown (region-lines) ---
    ax1 = fig.add_subplot(gs[0, :])
    y = np.arange(P)
    only_a = np.array([pairs[n]["only_a"] for n in names], dtype=float)
    shared = np.array([pairs[n]["shared"] for n in names], dtype=float)
    only_b = np.array([pairs[n]["only_b"] for n in names], dtype=float)
    ax1.barh(y, only_a, color=C_A)
    ax1.barh(y, shared, left=only_a, color=C_SHARED)
    ax1.barh(y, only_b, left=only_a + shared, color=C_B)
    totals = only_a + shared + only_b
    span = totals.max() if totals.size else 1.0
    for i, n in enumerate(names):
        ax1.text(totals[i], i, f"  J={pairs[n]['jaccard']:.3f}", va="center", fontsize=8)
        # Count labels on segments wide enough to hold text (avoid clutter on slivers).
        if only_a[i] > 0.04 * span:
            ax1.text(only_a[i] / 2, i, f"{int(only_a[i])}", ha="center", va="center",
                     fontsize=7, color="white")
        if only_b[i] > 0.04 * span:
            ax1.text(only_a[i] + shared[i] + only_b[i] / 2, i, f"{int(only_b[i])}",
                     ha="center", va="center", fontsize=7, color="white")
    ax1.set_yticks(y)
    ax1.set_yticklabels([f"{split_pair(n)[0]}  vs  {split_pair(n)[1]}" for n in names],
                        fontsize=8)
    ax1.invert_yaxis()
    ax1.set_xlabel("covered region-lines")
    ax1.set_title("Per-pair coverage overlap  (blue = only LEFT approach, grey = shared, "
                  "orange = only RIGHT approach)")
    ax1.legend(handles=[Patch(color=C_A, label="only left approach"),
                        Patch(color=C_SHARED, label="shared"),
                        Patch(color=C_B, label="only right approach")],
               fontsize=8, loc="lower right")
    ax1.grid(alpha=0.3, axis="x")

    # --- One by-function panel PER pair ---
    for pi, n in enumerate(names):
        r, c = divmod(pi, ncols)
        ax = fig.add_subplot(gs[1 + r, c])
        left, right = split_pair(n)
        byfn = pairs[n].get("by_function", [])[: args.top]
        if not byfn:
            ax.text(0.5, 0.5, f"{left} vs {right}\nno per-function differences",
                    ha="center", va="center", fontsize=9)
            ax.axis("off")
            continue
        labels = [short_fn(dm.get(d["fn"], d["fn"])) for d in byfn]
        oa = [d.get("only_a", 0) for d in byfn]
        ob = [d.get("only_b", 0) for d in byfn]
        yy = np.arange(len(labels))
        h = 0.4
        ax.barh(yy - h / 2, oa, height=h, color=C_A, label=f"only {left}")
        ax.barh(yy + h / 2, ob, height=h, color=C_B, label=f"only {right}")
        ax.set_yticks(yy)
        ax.set_yticklabels(labels, fontsize=6)
        ax.invert_yaxis()
        ax.set_xlabel("uniquely-covered region-lines")
        ax.set_title(f"{left}  vs  {right} — top {len(labels)} functions by disagreement",
                     fontsize=9)
        ax.legend(fontsize=7, loc="lower right")
        ax.grid(alpha=0.3, axis="x")

    # Hide any trailing empty grid cells (when P is odd and ncols == 2).
    for pi in range(P, nrows_fn * ncols):
        r, c = divmod(pi, ncols)
        fig.add_subplot(gs[1 + r, c]).axis("off")

    fig.suptitle("Input-driven validator line-coverage: overlap & per-pair function "
                 "differences (region-lines; harness excluded)", fontweight="bold")
    out = args.out or os.path.join(args.root, "coverage_compare.png")
    fig.savefig(out, dpi=130, bbox_inches="tight")
    print("wrote", os.path.abspath(out))


if __name__ == "__main__":
    main()
