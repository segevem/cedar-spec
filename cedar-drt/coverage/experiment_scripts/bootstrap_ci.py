#!/usr/bin/env python3
"""Bootstrap 95% confidence intervals around the MEDIAN, from repeated runs.

Reads per-rep analysis output written by `cedar-experiment analyze`
(``<root>/<approach>/analyze/rep_NN.json``), and for each approach/metric
computes the median across reps plus a percentile-bootstrap 95% CI around it.

The percentile bootstrap: resample the R per-run values with replacement B
times, take the median of each resample, and report the 2.5th / 97.5th
percentiles of those B medians as the CI. This makes no normality assumption
(appropriate for small R and for the median, which has no clean closed-form SE).

Writes ``<root>/bootstrap_ci.json`` and prints a table.
"""
import argparse
import json
import math
import os
import sys

import numpy as np

# metric key in rep json -> display label.  Callables derive from the record.
METRICS = [
    ("cumulative_3paths", "distinct 3-paths"),
    ("cumulative_2paths", "distinct 2-paths"),
    ("unique_inputs", "unique inputs"),
    ("unique_skeletons", "unique skeletons"),
    ("corpus_size", "corpus size (N)"),
    ("mean_node_count", "mean nodes/policy"),
    (lambda r: 100.0 * r["unique_inputs"] / r["corpus_size"] if r.get("corpus_size") else 0.0,
     "unique inputs (%)"),
    # Generator throughput (valid inputs/sec), merged from the throughput probe.
    ("throughput_valid_per_sec", "throughput (valid/s)"),
    # Input-driven validator line coverage (harness excluded), stamped by
    # coverage_analyze.py. Absent on reps not coverage-replayed -> skipped.
    ("source_lines_covered", "validator lines covered"),
]


def metric_value(rec, key):
    return float(key(rec)) if callable(key) else float(rec.get(key, 0) or 0)


def metric_name(key):
    return key if isinstance(key, str) else "unique_pct"


def load_reps(root, approach, reps):
    """Return the list of rep-json dicts that exist for an approach. Each analyze rec is
    augmented with `throughput_valid_per_sec` from that rep's throughput probe
    (throughput/rep_NN.json) so throughput can be reported alongside the analyze metrics."""
    out = []
    adir = os.path.join(root, approach, "analyze")
    tdir = os.path.join(root, approach, "throughput")
    for rep in range(reps):
        p = os.path.join(adir, f"rep_{rep:02d}.json")
        if not os.path.exists(p):
            continue
        with open(p) as f:
            rec = json.load(f)
        tp = os.path.join(tdir, f"rep_{rep:02d}.json")
        if os.path.exists(tp):
            try:
                with open(tp) as f:
                    rec["throughput_valid_per_sec"] = json.load(f).get("throughput_valid_per_sec")
            except (ValueError, OSError):
                pass
        out.append(rec)
    return out


def bootstrap_median_ci(vals, resamples, rng, alpha=0.05):
    """(median, ci_lo, ci_hi) via percentile bootstrap of the median."""
    vals = np.asarray(vals, dtype=float)
    n = len(vals)
    if n == 0:
        return (float("nan"),) * 3
    med = float(np.median(vals))
    if n == 1:
        return med, med, med
    idx = rng.integers(0, n, size=(resamples, n))
    boot_medians = np.median(vals[idx], axis=1)
    lo = float(np.percentile(boot_medians, 100 * alpha / 2))
    hi = float(np.percentile(boot_medians, 100 * (1 - alpha / 2)))
    return med, lo, hi


def exact_median_ci(vals, alpha=0.05):
    """Distribution-free CI for the median from order statistics.

    Returns (median, ci_lo, ci_hi, achieved_confidence). The interval
    [x_(k), x_(n+1-k)] with k the largest index whose lower Binomial(n, 1/2)
    tail is <= alpha/2 has guaranteed coverage >= 1-alpha (Thompson / sign-test
    interval). Unlike BCa, this is stable for the median at small n. When no k
    reaches the target level, falls back to [min, max] and reports the
    (lower) confidence actually achieved.
    """
    x = np.sort(np.asarray(vals, dtype=float))
    n = len(x)
    if n == 0:
        return (float("nan"),) * 3 + (float("nan"),)
    med = float(np.median(x))
    if n == 1:
        return med, med, med, 0.0

    def binom_cdf(k, n):  # P(X <= k), X ~ Binomial(n, 1/2)
        return sum(math.comb(n, i) for i in range(0, k + 1)) / (2 ** n)

    k = 0
    for kk in range(1, n // 2 + 1):
        if binom_cdf(kk - 1, n) <= alpha / 2:
            k = kk
        else:
            break
    if k == 0:  # cannot reach 1-alpha; widest interval is [min, max]
        conf = 1.0 - 2 * binom_cdf(0, n)  # excludes only the two extreme tails
        return med, float(x[0]), float(x[-1]), conf
    conf = 1.0 - 2 * binom_cdf(k - 1, n)
    return med, float(x[k - 1]), float(x[n - k]), conf


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True, help="experiment output root")
    ap.add_argument("--reps", type=int, required=True)
    ap.add_argument("--resamples", type=int, default=10000)
    ap.add_argument("--names", nargs="+", required=True, help="approach dir names")
    ap.add_argument("--seed", type=int, default=12345, help="bootstrap RNG seed (reproducibility)")
    ap.add_argument("--method", choices=["percentile", "exact", "both"], default="both",
                    help="percentile bootstrap of the median, exact order-statistic "
                         "(distribution-free, best at small n), or both")
    args = ap.parse_args()

    rng = np.random.default_rng(args.seed)
    result = {"resamples": args.resamples, "reps_requested": args.reps,
              "method": args.method, "approaches": {}}

    for name in args.names:
        recs = load_reps(args.root, name, args.reps)
        entry = {"reps_found": len(recs), "metrics": {}}
        for key, _label in METRICS:
            vals = [metric_value(r, key) for r in recs]
            m = {"n": len(vals), "values": vals}
            med, lo, hi = bootstrap_median_ci(vals, args.resamples, rng)
            m["median"] = med
            if args.method in ("percentile", "both"):
                m["ci_lo"], m["ci_hi"] = lo, hi
            if args.method in ("exact", "both"):
                _, elo, ehi, econf = exact_median_ci(vals)
                m["exact_ci_lo"], m["exact_ci_hi"], m["exact_conf"] = elo, ehi, econf
                if args.method == "exact":  # exact is the reported CI
                    m["ci_lo"], m["ci_hi"] = elo, ehi
            entry["metrics"][metric_name(key)] = m
        result["approaches"][name] = entry

    out_path = os.path.join(args.root, "bootstrap_ci.json")
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)

    # -------- printed table --------
    hdr = {"percentile": f"percentile bootstrap ({args.resamples} resamples)",
           "exact": "exact order-statistic (distribution-free)",
           "both": f"percentile bootstrap ({args.resamples} resamples)  |  exact order-statistic"}[args.method]
    print(f"\n95% CI around the median — {hdr}\n")
    for key, label in METRICS:
        mk = metric_name(key)
        print(f"== {label} ==")
        rows = []
        for name in args.names:
            m = result["approaches"][name]["metrics"].get(mk)
            nfound = result["approaches"][name]["reps_found"]
            if not m or m["n"] == 0:
                rows.append((name, "no data", nfound))
                continue
            txt = f"med {m['median']:.1f}"
            if "ci_lo" in m:
                txt += f"  boot[{m['ci_lo']:.1f}, {m['ci_hi']:.1f}]"
            if "exact_ci_lo" in m:
                txt += f"  exact[{m['exact_ci_lo']:.1f}, {m['exact_ci_hi']:.1f}]@{100*m['exact_conf']:.0f}%"
            rows.append((name, txt, nfound))
        w = max(len(r[0]) for r in rows)
        for nm, txt, nf in rows:
            print(f"  {nm:<{w}}  {txt:<52}  (n={nf})")
        print()

    if args.method in ("exact", "both") and result["approaches"]:
        any_n = next((e["reps_found"] for e in result["approaches"].values()), 0)
        if any_n and any_n < 12:
            print(f"NOTE: only ~{any_n} reps/approach — median CIs are coarse at small n. "
                  f"Raise REPS (>=12) for tighter intervals; the exact CI is the robust small-n choice.\n")

    print(f"Wrote {out_path}")


if __name__ == "__main__":
    sys.exit(main())
