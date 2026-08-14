# Specimen generator hangs (typeof-check / CapMerge)

Repro artifacts for inputs that cause the **Specimen generator** (not the DRT
target, not the typechecker) to spin indefinitely. These are generator
robustness gaps: `backtrackFuel` grinding through a combinatorial search on a
seed where the rule's constraint is (near-)unsatisfiable at the requested size.

---

## HANG-1 — `TypeOfCheck` / `CapMerge`, size 20

- **Discovered:** run `run-10min-20reps`, approach `typeof-check-sz20`, rep_02.
- **Commit:** `aed580429597114308610ce668bef06b2e2b5f73` (branch `relational-typeof`).
- **Symptom:** one refill spins at 100% CPU on a single core, flat RSS (~135 MB),
  zero output for 70+ min. Not I/O, not memory, not a mismatch — pure compute.

### Where it's stuck (gdb, thread 1 of the collect process)

Two snapshots ~1 min apart. Stack depth stable at ~134 frames (bounded — not a
stack-overflow path); top frame moving through the RNG each time (live search,
not a pinned frame):

```
#0  randNatAux → chooseNatLt            (snap1)   /   lean_apply_1 → Prod_map → randBound (snap2)
#4  Plausible.Gen.choose
#5  specimen.GeneratorCombinators.backtrackFuel
#6  CedarGen.Relational.Variants.TypeOfCheck …CapMerge…___lam__5
#8  lean_apply_2
#9  specimen.GeneratorCombinators.backtrackFuel
#10 …CapMerge…___lam__4
     … lam_3 → lam_4 → lam_5 → backtrackFuel → lam_… repeating ~30× …
```

Reading: the `CapMerge` rule of the `TypeOfCheck` variant sets up a generator
whose constraint is (near-)unsatisfiable for this seed at size 20;
`backtrackFuel` then explores an astronomically large but finite search,
redrawing random choices the whole way. Effectively non-terminating.

### Exact reproduction (deterministic — no instance needed)

The `lean-schema-typeof` generator ignores the driver loop seed and drives an
internal `next_seed` that starts at `start_seed` and advances by
`policies_per_schema` (= `CEDAR_BATCH_SIZE`, default **100**) per refill. Each
refill also yields ~100 valid inputs, so the stuck refill's seed
≈ `start_seed + (valid consumed)`.

- **Generator:** `lean-schema-typeof`  (FFI `generate_schema_typeof_proto`)
- **strategy:** `typeof-check`
- **size / schema_size:** `20` / `20`
- **count (policies_per_schema):** `100`
- **rep_02 config:** `--single-rep 2 --seed-base 0 --seed-stride 1000000000`
  → `start_seed = 2 × 1e9 = 2_000_000_000`
- **Refill seed sequence:** `2_000_000_000 + 100·k`  for k = 0, 1, 2, …
- **Hang location:** rep_02 had uploaded 98 corpus batches (~1000 inputs each)
  → ~98_000 valid consumed → stuck refill seed **≈ 2_000_098_000**
  (a multiple of 100, within ±~500 of that).

To pin the exact seed locally, replay refills from `2_000_000_000` in steps of
100 with a per-call wall-clock timeout; the first seed whose
`generate_schema_typeof_proto({seed, size:20, schema_size:20,
strategy:"typeof-check", count:100})` exceeds the timeout is the exact
offender. Then bisect within that batch (count:1, seed derived `seed+1..seed+100`)
to isolate the single hanging term-seed.

### Systemic fix (applies to ALL generators, not just this seed)

`run_collection_session` / `run_throughput_rep` call `generator.generate(seed)`
with no wall-clock guard, so one pathological seed stalls an entire rep forever
(here it also blocks the whole experiment's PHASE-2 `wait`). Add a per-generate
timeout: skip + log any seed whose generation exceeds e.g. 5 s. That converts
generator hotspots into logged data points instead of hangs, and makes long
unattended runs immune to this failure mode.
