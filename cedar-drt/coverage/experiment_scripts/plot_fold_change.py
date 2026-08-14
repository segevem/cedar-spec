#!/usr/bin/env python3
"""Fold-change diverging bar chart: which AST constructs a generator favors, and by how many x.

Pools the two specimen sizes (sz12+sz20) into one "specimen" and compares it to the handwritten
arm on a chosen per-construct METRIC:
  --metric composition  count / total_nodes   (share of all AST mass; diluted by Lit/Var padding)
  --metric per-policy   count / policies       (mean occurrences per policy)
  --metric presence     present / policies     (% of policies that contain it — "how often produced")
Bars shown for |fold| >= MINFOLD (the display threshold); constructs each side still favors below
that (down to COUNTFLOOR) are summarized as a "… + N more <side>-favored" ellipsis near the center,
so trimming the chart for a slide doesn't hide the breadth of the win. Positive = specimen-favored
(blue), negative = handwritten (orange); bar OPACITY ∝ prevalence (reference scale, upper-left);
each bar labeled with the multiple AND raw S=specimen / H=handwritten values.
Noise gate: a construct must be present in >= MINPRESENT of policies in its favored arm.

Usage: plot_fold_change.py --spec a.json b.json --hw c.json --out f.png --metric presence \
       --minfold 3 [--countfloor 1.5] [--minpresent 0.002]
"""
import argparse, json, math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
import numpy as np

SPEC_COLOR = "#2b6cb0"; HW_COLOR = "#dd6b20"; NEUTRAL = "#718096"


def pool(paths):
    counts, present, nodes, pols = {}, {}, 0, 0
    for p in paths:
        d = json.load(open(p)); nodes += d["total_nodes"]; pols += d["policies"]
        for k, v in d["counts"].items():  counts[k]  = counts.get(k, 0) + v
        for k, v in d["present"].items(): present[k] = present.get(k, 0) + v
    return counts, present, nodes, pols


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--spec", nargs="+", required=True); ap.add_argument("--hw", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--metric", default="composition", choices=["composition", "per-policy", "presence"])
    ap.add_argument("--title", default="Which AST constructs each generator favors")
    ap.add_argument("--minfold", type=float, default=3.0, help="DISPLAY threshold: bars shown for |fold|>=this")
    ap.add_argument("--countfloor", type=float, default=1.5, help="count (but don't draw) favored constructs down to this fold")
    ap.add_argument("--minpresent", type=float, default=0.002, help="noise gate: min policy-presence in favored arm")
    ap.add_argument("--spec-label", default="specimen"); ap.add_argument("--hw-label", default="handwritten")
    a = ap.parse_args()

    sc, sp, sn, spol = pool(a.spec)
    hd = json.load(open(a.hw)); hc, hp, hn, hpol = hd["counts"], hd["present"], hd["total_nodes"], hd["policies"]
    labels = set(sc) | set(hc)

    def rate(counts, present, nodes, pols, k):
        if a.metric == "composition": return counts.get(k, 0) / nodes
        if a.metric == "per-policy":  return counts.get(k, 0) / pols
        return present.get(k, 0) / pols
    MUNIT = {"composition": "% of nodes", "per-policy": "per policy", "presence": "% of policies"}[a.metric]

    def fmt(v):
        if a.metric == "per-policy": return f"{v:.2g}" if v >= 0.01 else "<0.01"
        p = v * 100; return f"{p:.2g}%" if p >= 0.01 else "<0.01%"

    lo = math.log2(a.countfloor); disp_l2 = math.log2(a.minfold)
    rows = []                 # displayed: [label, l2, txt, favored, only, rs, rh]
    extra = {"spec": 0, "hw": 0}   # favored below display threshold (countfloor..minfold)
    for k in labels:
        rs = rate(sc, sp, sn, spol, k); rh = rate(hc, hp, hn, hpol, k)
        ps = sp.get(k, 0) / max(spol, 1); ph = hp.get(k, 0) / max(hpol, 1)
        if rs > 0 and rh == 0:
            if ps < a.minpresent: continue
            rows.append([k, None, f"{a.spec_label}-only", "spec", "spec", rs, rh]); continue
        if rh > 0 and rs == 0:
            if ph < a.minpresent: continue
            rows.append([k, None, f"{a.hw_label}-only", "hw", "hw", rs, rh]); continue
        if rs == 0 and rh == 0: continue
        fold = rs / rh; l2 = math.log2(fold)
        favored = "spec" if l2 > 0 else "hw"
        if (ps if favored == "spec" else ph) < a.minpresent: continue
        if abs(l2) < lo: continue                    # below even the count floor -> ignore
        # ASYMMETRIC truncation: handwritten favors few constructs, so draw ALL of them down
        # to the count floor; specimen favors many, so only draw those >= the display threshold
        # and summarize the rest (countfloor..minfold) in an ellipsis.
        if favored == "spec" and abs(l2) < disp_l2:
            extra["spec"] += 1; continue
        rows.append([k, l2, f"{(fold if fold >= 1 else 1/fold):.1f}x", favored, None, rs, rh])
    if not rows:
        print("no significant constructs"); return

    finite = [abs(r[1]) for r in rows if r[1] is not None]
    onlymag = (max(finite) if finite else 1.0) * 1.25
    for r in rows:
        if r[1] is None: r[1] = onlymag if r[3] == "spec" else -onlymag
    rows.sort(key=lambda r: r[1])                     # hw (neg) bottom -> spec (pos) top

    lp = [math.log10(max(r[5], r[6])) for r in rows if max(r[5], r[6]) > 0]
    lpmin, lpmax = (min(lp), max(lp)) if lp else (-6.0, -2.0)
    def alpha_of(p):
        if lpmax <= lpmin: return 0.9
        return 0.30 + 0.65 * (math.log10(max(p, 1e-12)) - lpmin) / (lpmax - lpmin)

    # y-layout: a gap between the hw block (bottom) and specimen block (top) to hold the ellipsis.
    nhw = sum(1 for r in rows if r[1] < 0)
    GAP = 2.2 if (extra["spec"] or extra["hw"]) else 0.0
    ypos = [i if i < nhw else i + GAP for i in range(len(rows))]

    fig, ax = plt.subplots(figsize=(12.5, max(4.8, 0.5 * (len(rows) + GAP))))
    for i, (k, l2, txt, favored, only, rs, rh) in enumerate(rows):
        c = SPEC_COLOR if favored == "spec" else HW_COLOR
        ax.barh(ypos[i], l2, height=0.66, color=c, alpha=alpha_of(max(rs, rh)),
                hatch="//" if only else None, edgecolor=c, linewidth=1.0, zorder=3)
        ha = "left" if l2 > 0 else "right"
        ax.annotate(f"{txt}   (S {fmt(rs)} · H {fmt(rh)})", (l2, ypos[i]),
                    xytext=(5 * (1 if l2 > 0 else -1), 0), textcoords="offset points",
                    va="center", ha=ha, fontsize=9, color="#1a202c")
    # ellipsis rows in the gap
    if GAP:
        gy = nhw - 0.5 + GAP / 2.0
        band = f"{a.countfloor:g}–{a.minfold:g}x"
        if extra["spec"]:
            ax.annotate(f"⋯  + {extra['spec']} more {a.spec_label}-favored constructs ({band})",
                        (0, gy + 0.45), xytext=(8, 0), textcoords="offset points", va="center",
                        ha="left", fontsize=10, style="italic", color=SPEC_COLOR, fontweight="bold")
        if extra["hw"]:
            ax.annotate(f"⋯  + {extra['hw']} more {a.hw_label}-favored ({band})",
                        (0, gy - 0.45), xytext=(-8, 0), textcoords="offset points", va="center",
                        ha="right", fontsize=10, style="italic", color=HW_COLOR, fontweight="bold")

    ax.axvline(0, color=NEUTRAL, lw=1.5, zorder=2)
    ax.set_yticks(ypos); ax.set_yticklabels([r[0] for r in rows], fontsize=11)
    mx = max(abs(r[1]) for r in rows) + 4.2
    ticks = [t for t in range(-8, 9) if abs(t) <= mx]
    ax.set_xticks(ticks); ax.set_xticklabels([("1x" if t == 0 else f"{2**abs(t):d}x") for t in ticks], fontsize=10)
    ax.set_xlim(-mx, mx); ax.set_ylim(-1, (len(rows) + GAP))
    ax.set_xlabel(f"←  {a.hw_label} favors      ·      fold-change (log2)      ·      {a.spec_label} favors  →", fontsize=11)
    ax.set_title(f"{a.title}\nmetric = {a.metric} ({MUNIT}) · specimen shown ≥{a.minfold:g}x, "
                 f"handwritten shown ≥{a.countfloor:g}x · opacity = prevalence · S=specimen, H=handwritten", fontsize=11)
    ax.grid(axis="x", alpha=0.3, zorder=0)

    leg1 = ax.legend(handles=[Patch(color=SPEC_COLOR, label=f"{a.spec_label}-favored"),
                              Patch(color=HW_COLOR, label=f"{a.hw_label}-favored")],
                     loc="lower right", fontsize=10, framealpha=0.95)
    ax.add_artist(leg1)
    refs = np.linspace(lpmin, lpmax, 4)
    ax.legend(handles=[Patch(facecolor="#4a5568", alpha=alpha_of(10**e), edgecolor="none", label=fmt(10**e)) for e in refs],
              title=f"opacity = prevalence ({MUNIT})", loc="upper left", fontsize=9, title_fontsize=9,
              framealpha=0.95, handlelength=1.6)
    fig.tight_layout(); fig.savefig(a.out, dpi=140); print("wrote", a.out, "| extra:", extra)


if __name__ == "__main__":
    main()
