---
name: symcc-coverage-differences
description: "SymCC never-errors 1h run: line-coverage + k-path coverage differences across wt-policy sz12/sz20 vs hw-symcc-plain"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 80b33588-72ac-4fb9-a607-0ff17df90158
  modified: 2026-08-07T16:18:37.862Z
---

# SymCC never-errors coverage differences (1h run, 2026-08-07)

Run: S3ROOT `ci-run-20reps-3600s-20260807T041143Z` (TARGET symcc-term-never-errors, 3 arms:
symcc-wt-policy-sz12, symcc-wt-policy-sz20, hw-symcc-plain; 20 reps, 1h window). Coverage scoped to
the symbolic COMPILER (INSTRUMENT_CRATES=cedar_policy_symcc; validator excluded — see
[[symcc-nevererrors-target]]). Graphs saved: `~/symcc_2size_1h_graphs/` (+ `~/validation_2size_1h_graphs/`).

## LINE coverage (cedar-policy-symcc)
Totals near-identical: sz20 **2501** ≈ sz12 **2493** > hw **2454** (~2%). The interesting part is WHICH lines.
- **Specimen-unique (~42 lines, both sizes):** `symcc::enforcer::transitivity` (+closures) = **24** (action-hierarchy
  transitivity SMT enforcement — direct payoff of the transitive-closure generator fix; hw never drives it),
  `env::SymEntityData::of_entity_type` closures (9), `extension_types::ipaddr::IPv4Prefix/IPv4Addr::try_from_bitvec` (9),
  `factory::app` closure (2).
- **hw-unique:** `ipaddr::to_hex_nat` (2, always); `extfun::offset` (7) + `symccopt::compiler::compile_call` (2)
  vs **sz12 ONLY** — sz20 CLOSES the offset gap (offset shared with sz20). So the offset blind spot is a SIZE
  artifact (sz12 too small to reach offset calls), not fundamental.
- Size effect on line coverage: tiny (~8 lines); the main gain is sz20 covering `extfun::offset`.

## Treemap: only the term-construction HALF is covered (~34%, 2423/7151 region-lines)
never-errors only GENERATES+COMPARES the SMT Asserts (Terms) — it never solves/decodes. So:
- COVERED (term construction): factory, env, extfun, term_type, bitvec, datetime, ipaddr, enforcer(partial),
  `symccopt::compiler` (~100% — the OPTIMIZED compiler Rust runs via CompiledPolicy::compile).
- RED/uncovered (solve+decode half): solver, solver_pool, symbolizer, concretizer, decoder, encoder, extractor,
  smtlib_script, interpretation, symcc::verifier, AND `symcc::compiler` (the REFERENCE compiler — red because Rust
  runs symccopt, not the reference; the reference is Lean's mirror).
- NOTHING is excluded from instrumentation (whole crate instrumented); red = instrumented-but-not-executed. To cover
  the solve half you'd need a `symcc-check-*-ok` target (invokes cvc5).

## K-PATHS (3-paths)
per-rep median: sz20 **3238** > hw **2398** > sz12 **2203** (hw>sz12 at 1h = the graph crossover; at 15min sz12>hw).
union(20): sz20 4213 > hw 3611 > sz12 2684. union/median: sz12 **1.22** (tight/convergent), sz20 1.30, hw **1.51**
(high variance — same story as validation [[run3-operator-frequency]]/welltyped runs). shared-by-all=1876.
- Size: sz20\sz12 = **1694** (depth); sz12\sz20 = 165.
- spec-only(not hw) = **1598**: arithmetic 30%, tags 24%, ext-fn 53%, if 50%, set-ops 15%.
- hw-only(not spec) = **831**: ext-fn **79%**, if 54%, set-ops 32%, tags 6%, **arithmetic 0%** (hw contributes ZERO
  unique arithmetic paths).

## SYNTHESIS
Specimen's edge is QUALITATIVE/structural (transitivity enforcement, arithmetic terms, tags); handwritten's edge is
ext-fn VARIETY (offset etc.) — but that's largely SIZE-fixable (sz20 closes offset + adds ext-fn depth). Per-run
specimen ≥ hw on line coverage (near-superset, J≈0.98) AND is the more reproducible (tiny variance); handwritten's
value is its stochastic breadth in the k-path union. Both complementary.

## NODE / EXT-FN HISTOGRAM (2026-08-07) — FULL-CORPUS rare-op rates
Method (FINAL): `op_hist` over the ENTIRE corpus, all 20 reps/arm — **74.2M** (sz12) / **7.08M** (sz20) /
**25.7M** (hw) policies. `op_hist` recurses a dir and accumulates ONE merged tally, so per-rep runs (60 in
parallel on the c7i, ~35s total) just sum; the 30GB sz12 S3 pull was the only slow part (~11min). Plot:
`experiment_scripts/plot_node_hist.py --json merged_hist.json` (grouped barh, nodes/policy, log x; script now
committed — it was ad-hoc before). merged_hist.json archived at s3://…/041143Z/debug/merged_hist.json.
The full-corpus rates VALIDATED the earlier 48-batch sample almost exactly (avg nodes/policy 18.35/27.73/5.92
vs sampled 18.3/27.6/5.7) — the sample was reliable for common ops; full corpus was needed only to be certain
of the ext-fn tail. LESSON: a 12-batch sample MISSES rare ops (<~0.01/policy); 48-batch was adequate; full
corpus is definitive.
- Policy SIZE dominates: avg nodes/policy sz20 **27.6** > sz12 **18.3** > hw **5.7** (specimen 3-5x bigger —
  root of the per-run coverage/k-path lead). Common-op contrasts (nodes/policy): specimen denser in
  HasTag ~80x, Unary::Not ~30x, Is ~8x than hw.
- EXT-FN rates (nodes/policy, sz12 / sz20 / hw): datetime .119/.295/.029; duration .107/.259/.024;
  ip .037/.103/.045; decimal .022/.082/.017; toDate .011/.026/.002; toTime .010/.024/.001;
  isIpv4/isIpv6/isLoopback ~.008/.021/.003; isMulticast .007/.020/.010; decimal-cmps (lessThan/greaterThan/…)
  ~.003/.010/.001; to{Hours,Days,Seconds,Minutes,Ms} ~.001/.005/.0001; **offset .0000/.013/.012**;
  **durationSince .0001/.012/.001**. Specimen (esp sz20) is denser than hw in NEARLY EVERY ext-fn.
- CORRECTIONS to earlier small-sample claims:
  * `isEmpty` is NOT a specimen gap — present at BOTH sizes/all 20 reps (nodes/policy sz12 .0001, sz20 .0004,
    hw .0055 — hw ~14-55x denser but specimen NONZERO). Initial "specimen=0 isEmpty" was a 12-batch miss;
    coverage maps correctly show it covered by specimen (not hw-unique).
  * `durationSince` is NOT a gap either — present at sz12 (.0001), and sz20 (.012) > hw (.001).
  * The ONLY genuine specimen ext-fn gap is **`offset` at sz12** (0 over the FULL 74.2M-policy corpus — the one
    and only constructor absent at sz12, 47 distinct ops vs 48; also 0/781M 2-paths, 0 of 20 reps); sz20 closes
    it (.0133 ≈ hw .0118). Size-gated; quadruple-confirmed (full-corpus op_hist + kpath + coverage_compare + sample).
  * hw is denser than specimen ONLY in `isEmpty` (~14x) and `offset`@sz12; on virtually every other ext-fn
    specimen (esp sz20) leads. hw's coverage-map "ext-fn edge" was just offset@sz12 + internal `ipaddr::to_hex_nat`.

## Deferred follow-ups (user chose "just document" 2026-08-07; NOT done)
- Close the ext-fn/offset gap for sz12 via a datetime/ext-fn weight modifier (like the hasTag tuning
  [[specimen-weight-modifier]]).
- Add a solver-path `symcc-check-never-errors-ok` target to cover the solve/decode half (needs CVC5 on the instance).
- Combined specimen+handwritten UNION-corpus coverage analysis (they're complementary).
Both 1h instances (validation i-0dbb2550a5477dcc9, symcc i-0a30416229ef8b0d2) STOPPED, reusable; do NOT kill w/o direction.

## PLOTTING + REPLAY FIXES (2026-08-07) — addresses the two follow-ups below
Root cause of the ci-run-…041143Z guided coverage gaps: the PHASE 3.5 replay listed some guided reps'
S3 corpora BEFORE their async drain uploads settled → shards streamed 0 inputs → whole reps replayed
0/16 (silently empty; corpora were fully present minutes later). Confirmed by a re-run on the settled
corpora: 0 failed shards, all 20 reps, SAME union totals (hw 2454 / sz12 2493 / sz20 2501 — coverage
saturates, so totals were never wrong; only the over-time curves + n were). NOT threads (that fix held:
main.rs replay uses new_current_thread) and NOT memory (no rss limit in replay).
FIXES (working tree, for future runs):
1. run_experiment.sh: NEW PHASE-3.5 upload BARRIER — before replay, per approach×rep wait until the S3
   corpus prefix is non-empty AND object count is stable across 2 checks. Prevents the list-before-upload race.
2. plot_over_time.py (FINAL, 2026-08-07): KEEP-ALL-non-degenerate (drop only reps with s[0][-1]<=0, i.e. a
   truly failed/zero-coverage replay) + grid to the LONGEST-run endpoint + FORWARD-FILL each rep past its
   last snapshot (plain np.interp flat clamp) + median over ALL reps at every grid point. Label is just
   `(n=X)`. RATIONALE: all metrics are CUMULATIVE and every non-degenerate rep ran the full fixed window, so
   holding the last value is honest, not extrapolation. This gives constant n across the axis (no tail taper)
   AND a monotonic median (median of monotonic rows is monotonic).
   ⚠️ DEAD ENDS I already hit — do NOT reintroduce: (a) grid-to-MAX WITHOUT forward-fill → sub-second endpoint
   differences (reps end 3600.1 vs 3600.9s) put one rep alone in the last grid cell → cumulative median SPIKES
   to that single fast rep. (b) MASK-beyond-own-data (NaN tail) → median recomputed over a shrinking self-
   selected cohort → n tapers to ~half (n=20→10) AND the "cumulative" median moves DOWN at the tail when the
   earliest-ending reps are the high-coverage ones (impossible for a cumulative quantity — user caught this).
   (c) drop-incomplete `<0.9*probe_end` → wrongly dropped ~half of guided reps (validation hw n=8).
DONE: BOTH graph sets regenerated with the final plot + re-run/complete per-rep data and installed:
  ~/symcc_2size_1h_graphs/ (n=20/20/20) and ~/validation_2size_1h_graphs/ (wt n=20/20, hw-slots-off n=19 —
  rep_06 genuinely degenerate: 0 covered lines, a real shard-race casualty in the NON-re-run 041135Z run).
  Originals preserved in each folder's pre_medianfix_backup/. Per-rep JSON bundles archived at
  s3://…/{041143Z,041135Z}/debug/{symcc,val}_perrep_rerun.tgz (analyze+throughput+coverage over_time+manifest).
  Both 192-vCPU instances STOPPED again.
