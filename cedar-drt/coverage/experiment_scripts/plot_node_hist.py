#!/usr/bin/env python3
"""Grouped horizontal bar chart of AST node / operator / ext-fn frequency.

Reads a merged op_hist tally (see src/bin/op_hist.rs --json) of the form
    {"<arm>": {"counts": {"<label>": <total>, ...}, "present": {"<label>": <#policies>, ...},
               "policies": <N>, "total_nodes": <M>}, ...}
and plots one of three x-axis metrics (grouped bar per arm per label):
  --metric composition     (DEFAULT) count / total_nodes * 100  = node type's SHARE of all AST
                           mass. Size-invariant, a true distribution, best for comparing the node
                           MIX between generators (and spotting under-represented constructs).
  --metric present-pct     present / policies * 100  = % of policies containing the node >=once.
                           Best for "does the generator ever emit X / in how many policies".
  --metric per-policy      count / policies  = mean occurrences per policy (confounded by size).

Scale: LINEAR by default (pass --logx for log, useful only when you must see the rare tail).
Highlights: the labels with the largest cross-arm spread (max-min across arms) are shaded and
bolded, and the delta is annotated — so the constructs where the generators most DIFFER pop out.
Sort: by max value (densest at top) by default; --sort diff sorts by cross-arm spread instead.

Usage: plot_node_hist.py --json merged_hist.json --out hist.png [--metric composition] \
       [--title "..."] [--order arm1,arm2,arm3] [--strip-prefix symcc-] [--logx] \
       [--highlight 8] [--sort max|diff]
"""
import argparse
import json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

# Stable arm -> color so sz12/sz20/hw keep the same hue across every figure.
COLOR = {
    "symcc-wt-policy-sz12": "tab:blue", "wt-policy-sz12": "tab:blue",
    "symcc-wt-policy-sz20": "tab:purple", "wt-policy-sz20": "tab:purple",
    "hw-symcc-plain": "tab:orange", "hw-slots-off": "tab:orange",
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--metric", default="composition",
                    choices=["composition", "present-pct", "per-policy"])
    ap.add_argument("--title", default=None)
    ap.add_argument("--order", default="", help="comma-sep arm order; default = json key order")
    ap.add_argument("--strip-prefix", default="", help="prefix to drop from legend labels")
    ap.add_argument("--logx", action="store_true", help="log x-axis (default linear)")
    ap.add_argument("--highlight", type=int, default=8,
                    help="shade+bold the N labels with the largest cross-arm spread (0=off)")
    ap.add_argument("--sort", default="max", choices=["max", "diff"],
                    help="order labels by max value (default) or by cross-arm spread")
    args = ap.parse_args()

    res = json.load(open(args.json))
    arms = [a for a in args.order.split(",") if a] if args.order else list(res.keys())
    arms = [a for a in arms if a in res]

    unit = "log scale" if args.logx else "linear"
    XLABEL = {
        "composition": f"share of all AST nodes (%, {unit})",
        "present-pct": f"policies containing the node (%, {unit})",
        "per-policy":  f"occurrences per policy ({unit})",
    }[args.metric]
    DEFTITLE = {
        "composition": "AST node / operator / ext-fn — share of all nodes (%)",
        "present-pct": "AST node / operator / ext-fn — % of policies containing it",
        "per-policy":  "AST node / operator / ext-fn — occurrences per policy",
    }[args.metric]

    # value per label per arm, per the chosen metric; union of all labels seen in any arm
    rate = {}
    for a in arms:
        pol = max(int(res[a].get("policies", 0)), 1)
        nodes = max(int(res[a].get("total_nodes", 0)), 1)
        counts = res[a].get("counts", {})
        present = res[a].get("present", {})
        if args.metric == "composition":
            rate[a] = {k: 100.0 * v / nodes for k, v in counts.items()}
        elif args.metric == "present-pct":
            rate[a] = {k: 100.0 * v / pol for k, v in present.items()}
        else:  # per-policy
            rate[a] = {k: v / pol for k, v in counts.items()}

    all_labels = {k for a in arms for k in rate[a]}
    spread = {k: (max(rate[a].get(k, 0.0) for a in arms) - min(rate[a].get(k, 0.0) for a in arms))
              for k in all_labels}
    maxval = {k: max(rate[a].get(k, 0.0) for a in arms) for k in all_labels}
    keyfn = spread if args.sort == "diff" else maxval
    labels = sorted(all_labels, key=lambda k: keyfn[k], reverse=True)
    # labels to highlight = largest cross-arm spread (the constructs the generators differ on most)
    hl = set(sorted(all_labels, key=lambda k: spread[k], reverse=True)[:max(args.highlight, 0)])

    n_arms = len(arms)
    y = np.arange(len(labels))
    h = 0.8 / n_arms
    fig, ax = plt.subplots(figsize=(11.5, max(6, 0.34 * len(labels))))
    floor = 1e-4 if args.logx else 0.0
    for i, a in enumerate(arms):
        vals = [rate[a].get(k, 0.0) for k in labels]
        if args.logx:
            # log: a genuinely-absent op draws NO bar (NaN), a rare-but-present one gets a floor stub.
            widths = [max(v, floor) if v > 0 else np.nan for v in vals]
            left = floor
        else:
            widths = vals
            left = 0.0
        ax.barh(y - 0.4 + h / 2 + i * h, widths,
                height=h, left=left, color=COLOR.get(a, f"C{i}"),
                label=(a[len(args.strip_prefix):] if args.strip_prefix and a.startswith(args.strip_prefix) else a))

    # Highlight rows with the largest cross-arm spread: shaded band, bold label, delta annotation.
    xmax_data = max((maxval[k] for k in labels), default=1.0)
    for j, k in enumerate(labels):
        if k in hl:
            ax.axhspan(j - 0.5, j + 0.5, color="gold", alpha=0.16, zorder=0)
            d = spread[k]
            xa = max(maxval[k], floor)
            ax.annotate(f"Δ{d:.2g}", (xa, j), textcoords="offset points", xytext=(6, 0),
                        va="center", fontsize=7, color="0.25", fontweight="bold")
    ax.set_yticks(y)
    ax.set_yticklabels(labels, fontsize=8)
    for tick, k in zip(ax.get_yticklabels(), labels):
        if k in hl:
            tick.set_fontweight("bold")
    ax.invert_yaxis()                       # densest (first) label at top
    if args.logx:
        ax.set_xscale("log")
        ax.set_xlim(left=floor)
    else:
        ax.set_xlim(left=0, right=xmax_data * 1.12)   # headroom for the Δ annotations
    ax.set_xlabel(XLABEL)
    ttl = args.title or DEFTITLE
    if hl:
        ttl += f"\n(gold rows = {len(hl)} constructs with largest generator differences; Δ = max−min across arms)"
    ax.set_title(ttl)
    ax.legend(loc="lower right")
    ax.grid(axis="x", alpha=0.3)
    fig.tight_layout()
    fig.savefig(args.out, dpi=130)
    print("wrote", args.out)


if __name__ == "__main__":
    main()
