#!/usr/bin/env python3
"""Coverage-over-time overlay: all lines (dashed) vs error+annotation excluded (solid).

x = REAL wall-clock generation time, from each run's throughput probe
(corpus_idx == cumulative valid_count generated -> elapsed_secs). Coverage is sampled at
the replay's shard boundaries, so we plot the ACTUAL sample points (markers) connected by
straight lines — the segments between samples are interpolation, NOT measured data. Each
curve starts at (t=0, coverage=0): before any input is generated, nothing is covered.
"""
import argparse, glob, json, os
import numpy as np
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

COLORS = ["#1f77b4", "#d62728", "#2ca02c", "#9467bd", "#ff7f0e"]


def _med_ci(vals, rng, resamples=5000):
    """(median, lo95, hi95) — 95% bootstrap CI OF THE MEDIAN over reps (matches the band method)."""
    v = np.asarray(vals, dtype=float)
    m = float(np.median(v))
    if len(v) <= 1:
        return m, m, m
    boot = np.median(v[rng.integers(0, len(v), size=(resamples, len(v)))], axis=1)
    return m, float(np.percentile(boot, 2.5)), float(np.percentile(boot, 97.5))


def early_band(early_dir, name, window, rng, key="covered_lines_excl", gpts=80):
    """Fine first-`window`-seconds coverage over ALL reps -> (grid, median, lo95, hi95) via the
    same median + 95% bootstrap-CI-of-the-median method as the main curve, so the early region
    carries a proper CI BAND. Each rep anchored at (0,0), NaN past its last sample."""
    eg = np.linspace(0.0, window, gpts)
    M = []
    for rep in range(40):
        p = os.path.join(early_dir, name, f"rep_{rep:02d}_early.json")
        if not os.path.exists(p):
            continue
        s = json.load(open(p))
        if not s:
            continue
        x = np.array([0.0] + [d["elapsed_secs"] for d in s], dtype=float)
        y = np.array([0.0] + [d.get(key, d["covered_lines"]) for d in s], dtype=float)
        yi = np.interp(eg, x, y); yi[eg > x[-1]] = np.nan
        M.append(yi)
    if not M:
        return None
    em, el, eh = boot_median_ci(np.vstack(M), rng)
    return eg, em, el, eh


def early_two_points(early_dir, name, window, rng, key="covered_lines_excl"):
    """Two measured points for an arm from cov_early.py's <arm>/rep_NN_early.json — the FIRST
    measured sample and the value at t=`window` — each with a 95% bootstrap CI of the median over
    ALL reps. Returns ((t1,y1,y1lo,y1hi),(t2,y2,y2lo,y2hi)) or None."""
    t1s, y1s, y2s = [], [], []
    for rep in range(40):
        p = os.path.join(early_dir, name, f"rep_{rep:02d}_early.json")
        if not os.path.exists(p):
            continue
        s = json.load(open(p))
        if not s:
            continue
        x = np.array([d["elapsed_secs"] for d in s], dtype=float)
        y = np.array([d.get(key, d["covered_lines"]) for d in s], dtype=float)
        t1s.append(x[0]); y1s.append(y[0]); y2s.append(float(np.interp(window, x, y)))
    if not t1s:
        return None
    y1, y1lo, y1hi = _med_ci(y1s, rng)
    y2, y2lo, y2hi = _med_ci(y2s, rng)
    return (float(np.median(t1s)), y1, y1lo, y1hi), (window, y2, y2lo, y2hi)

def timemap(root, name, rep):
    # Prefer the COLLECT's own timeline (what produced the corpus); fall back to the throughput
    # probe for fused arms. See plot_over_time.py:time_map for the full rationale.
    p = os.path.join(root, name, "collect", f"_fuzz_stats_rep_{rep:02d}.json")
    if os.path.exists(p):
        sn = json.load(open(p)).get("snapshots", [])
        if sn:
            return (np.array([0.0]+[x[1] for x in sn]),
                    np.array([0.0]+[x[0]/1000.0 for x in sn]))
    p = os.path.join(root, name, "throughput", f"rep_{rep:02d}.json")
    if os.path.exists(p):
        sn = json.load(open(p)).get("snapshots", [])
        if sn and isinstance(sn[0], dict):
            return (np.array([0.0]+[x["valid_count"] for x in sn]),
                    np.array([0.0]+[x["elapsed_secs"] for x in sn]))
    p = os.path.join(root, name, "throughput", f"_fuzz_stats_rep_{rep:02d}.json")
    if os.path.exists(p):
        sn = json.load(open(p)).get("snapshots", [])
        if sn:
            return (np.array([0.0]+[x[1] for x in sn]),
                    np.array([0.0]+[x[0]/1000.0 for x in sn]))
    return None

def load_rep(root, name, rep):
    p = os.path.join(root, name, "coverage", f"rep_{rep:02d}_over_time.json")
    if not os.path.exists(p): return None
    s = json.load(open(p))
    if not s or "corpus_idx" not in s[0]: return None
    ci  = np.array([d["corpus_idx"] for d in s], float)
    raw = np.array([d["covered_lines"] for d in s], float)
    exc = np.array([d.get("covered_lines_excl", d["covered_lines"]) for d in s], float)
    tm = timemap(root, name, rep)
    x = np.interp(ci, tm[0], tm[1]) if tm else ci
    return x, raw, exc

def boot_median_ci(M, rng, resamples=5000):
    """Per-column MEDIAN across reps + 95% bootstrap CI OF THE MEDIAN (resample reps)."""
    n = M.shape[0]
    med = np.median(M, axis=0)
    if n <= 1:
        return med, med.copy(), med.copy()
    idx = rng.integers(0, n, size=(resamples, n))
    boot = np.median(M[idx], axis=1)               # [resamples, L]
    lo = np.percentile(boot, 2.5, axis=0)
    hi = np.percentile(boot, 97.5, axis=0)
    return med, lo, hi

def agg(root, name, reps, rng, prepend=True):
    xs, rs, es = [], [], []
    for r in range(reps):
        g = load_rep(root, name, r)
        if g is None or len(g[0]) < 2: continue
        xs.append(g[0]); rs.append(g[1]); es.append(g[2])
    if not xs: return None
    L = min(len(a) for a in xs)                       # align by shard-boundary index
    X = np.vstack([a[:L] for a in xs]); R = np.vstack([a[:L] for a in rs]); E = np.vstack([a[:L] for a in es])
    n = X.shape[0]
    mx = np.median(X, 0)                                        # representative sample time per shard boundary
    mr, mr_lo, mr_hi = boot_median_ci(R, rng)                  # all-lines (dashed): median + 95% CI of median
    me, me_lo, me_hi = boot_median_ci(E, rng)                  # excluded (solid):   median + 95% CI of median
    # prepend the true origin (t=0, coverage=0) UNLESS early dots will own the opening region — a
    # fabricated (0,0)->first-sample ramp would visually contradict the measured dots.
    o = (lambda a: np.concatenate([[0.0], a])) if prepend else (lambda a: a)
    return o(mx), o(mr), o(mr_lo), o(mr_hi), o(me), o(me_lo), o(me_hi), n

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True); ap.add_argument("--reps", type=int, default=20)
    ap.add_argument("--out", default=None)
    ap.add_argument("--ymin", type=float, default=0.0)
    ap.add_argument("--ymax", type=float, default=None, help="set with --ymin for a zoomed view")
    ap.add_argument("--zoom", action="store_true", help="auto-zoom y to the data range (excluded+all series)")
    ap.add_argument("--early", default=None,
                    help="dir with <arm>/rep_NN_early.json (cov_early.py); drawn in a first-30s INSET")
    ap.add_argument("--early-window", type=float, default=30.0)
    ap.add_argument("--inset-rect", type=float, nargs=4, default=[0.20, 0.30, 0.40, 0.44],
                    metavar=("X0", "Y0", "W", "H"),
                    help="inset position (axes fraction) for the first-30s early detail")
    ap.add_argument("--xscale", default="linear", choices=["linear", "symlog"],
                    help="symlog makes the first-30s dots legible alongside the full hour")
    a = ap.parse_args()
    mf = os.path.join(a.root, "manifest.json")
    names = [x["name"] for x in json.load(open(mf))["approaches"]] if os.path.exists(mf) \
        else sorted(d for d in os.listdir(a.root) if os.path.isdir(os.path.join(a.root, d, "coverage")))
    rng = np.random.default_rng(2024)
    fig, ax = plt.subplots(figsize=(10, 6.2))
    rows = []
    for i, name in enumerate(names):
        g = agg(a.root, name, a.reps, rng, prepend=True)
        if g is None: continue
        rows.append((g, COLORS[i % len(COLORS)], name))
    # Plot REAL samples only. A healthy guided arm count-matches the probe (corpus == hour-count)
    # so it spans the full run naturally; an arm that ends short did NOT count-match (collect died /
    # dropped inputs) — a real defect to see, not to paper over with a held tail.
    for g, c, name in rows:
        mx, mr, mr_lo, mr_hi, me, me_lo, me_hi, n = g
        # actual sample points + straight-line segments (segments are interpolation, not data).
        # Central line = per-run MEDIAN; band = 95% bootstrap CI OF THE MEDIAN. Plain overlaid look.
        plt.plot(mx, mr, "--o", color=c, alpha=0.45, lw=1.3, ms=4, label=f"{name} — all lines")
        plt.fill_between(mx, mr_lo, mr_hi, color=c, alpha=0.10)   # 95% CI of the median (dashed / all-lines)
        plt.plot(mx, me, "-o",  color=c, lw=2.0, ms=4.5, label=f"{name} — error+annotation excluded (n={n})")
        plt.fill_between(mx, me_lo, me_hi, color=c, alpha=0.12)   # 95% CI of the median (solid / excluded)

    # Early detail lives in an INSET (main axes stay the plain overlaid graph): first `window` seconds
    # of the EXCLUDED curve at full resolution — per-arm median + 95% CI band + the 2 measured dots.
    drew_early = False
    if a.early:
        axin = ax.inset_axes(a.inset_rect)
        for i, name in enumerate(names):
            c = COLORS[i % len(COLORS)]
            band = early_band(a.early, name, a.early_window, rng, "covered_lines_excl")
            if not band:
                continue
            eg, em, el, eh = band
            axin.fill_between(eg, el, eh, color=c, alpha=0.15)
            axin.plot(eg, em, "-", color=c, lw=1.8)
            pts = early_two_points(a.early, name, a.early_window, rng, "covered_lines_excl")
            if pts:
                (t1, y1, *_), (t2, y2, *_) = pts
                axin.plot([t1, t2], [y1, y2], "o", color=c, ms=5, mec="white", mew=0.7, zorder=6)
            drew_early = True
        axin.set_xlim(0, a.early_window); axin.set_ylim(bottom=0)
        axin.set_title(f"first {int(a.early_window)}s (excluded, measured)", fontsize=8)
        axin.tick_params(labelsize=7); axin.grid(alpha=0.3)
    if a.zoom and rows:
        # zoom to the PLATEAU (settled region: second half of the time axis) across BOTH series
        # (g=(mx,mr,mr_lo,mr_hi,me,me_lo,me_hi,n)) so the near-saturated arms are legible; the early
        # rise + wide early CI would otherwise force a low floor and squash the plateau.
        los, his = [], []
        for g, *_ in rows:
            mx = g[0]
            if len(mx) < 2:
                continue
            keep = mx >= mx[-1] * 0.5
            los.append(g[2][keep]); los.append(g[5][keep])   # all-lines & excluded CI floors
            his.append(g[3][keep]); his.append(g[6][keep])   # ...and ceilings
        if los:
            lo_, hi_ = float(np.nanmin(np.concatenate(los))), float(np.nanmax(np.concatenate(his)))
            pad = max((hi_ - lo_) * 0.12, 1.0)
            a.ymin, a.ymax = lo_ - pad, hi_ + pad
    subtitle = "solid = error+annotation excluded · dashed = all lines · starts at (0,0)"
    if drew_early:
        subtitle = (f"solid = error+annotation excluded · dashed = all lines · "
                    f"inset = measured first {int(a.early_window)}s (median + 95% CI)")
    if a.xscale == "symlog":
        ax.set_xscale("symlog", linthresh=max(a.early_window, 1.0))
    plt.xlabel("wall-clock generation time (s) — from throughput probe")
    plt.ylabel("covered region-lines")
    plt.title("Line coverage over time — per-run median + 95% bootstrap CI\n" + subtitle, fontsize=10)
    plt.ylim(bottom=a.ymin, top=a.ymax); plt.xlim(left=0)
    plt.grid(alpha=0.3)
    handles, labels = ax.get_legend_handles_labels()
    out = a.out or os.path.join(a.root, "over_time_source_lines_excluded.png")
    if a.early:
        # Self-contained "overlaid" graph with the early detail in an inset: legend INLINE.
        ax.legend(handles=handles, fontsize=8, ncol=2, framealpha=0.95)
        plt.tight_layout(); plt.savefig(out, dpi=130); print("saved", out)
        return
    # Default (non-early): full-width graph with NO legend (avoids squishing); SEPARATE legend image.
    plt.tight_layout(); plt.savefig(out, dpi=130); print("saved", out)
    legout = os.path.splitext(out)[0] + "_legend.png"
    figl = plt.figure(figsize=(6.5, 2.2))
    figl.legend(handles, labels, loc="center", ncol=1, fontsize=10, frameon=True)
    figl.savefig(legout, dpi=130, bbox_inches="tight"); print("saved", legout)

if __name__ == "__main__":
    main()
