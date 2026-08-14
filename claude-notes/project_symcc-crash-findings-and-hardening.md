---
name: symcc-crash-findings-and-hardening
description: symcc-term-never-errors DRT surfaced two real findings (Lean tagNotFound on well-typed policy; Lean-vs-Rust term operand-order divergence); hardened the harness to collect+continue instead of panic=abort
metadata: 
  node_type: memory
  type: project
  modified: 2026-08-13T17:33:28.742Z
  originSessionId: 80b33588-72ac-4fb9-a607-0ff17df90158
---

# symcc DRT crashes = real findings; harness hardened (2026-08-12)

The boosted welltyped generator (tag-heavy) drove the `symcc-term-never-errors` coverage/DRT
target into two HARD ABORTS (core dumps) per the boost-lossless symcc rerun logs. Both are REAL
findings, not infra flakiness — and the harness was aborting because it `.unwrap()`/`assert!`ed
under `panic=abort` (so `catch_violation`'s `catch_unwind` couldn't catch → whole rep died).

## Finding 1 — Lean `tagNotFound` on a (supposedly) well-typed policy (target.rs:281)
`asserts_of_check_never_errors(...).unwrap()` unwrapped `Err(LeanBackendError("failed to compile
policy for requestEnv (…Action::\"d\"…): typeError for policy0: Cedar.Validation.TypeError.tagNotFound
{ id:=\"id\", path:=[\"e\",\"e\"] } (lit (string \"owner\")) "))`. i.e. the Lean symbolic compiler
refused a well-typed policy because Lean's validator threw `tagNotFound` on a `getTag(…,"owner")`.
NOT CONFIRMED to be the record-projection order-sensitivity bug ([[drt-mismatch-tagnotfound-record-projection]]) —
could equally be a generator soundness gap (getTag without a guarding hasTag slipping through). MUST
inspect the captured policy to decide. (Don't assume — this was explicitly flagged.)

## Finding 2 — Lean-vs-Rust symcc TERM divergence: operand order in `or` (target.rs:283)
`assert_that_asserts_match` compares `BTreeSet<Term>` and `Term` eq is STRUCTURAL, so
`or(A,B) != or(B,A)`. The crash diff showed the two compilers emit the SAME formula with the two
`or` operands flipped: left `or(eq(ite…), not(set.member("e", tagKeys…)))` vs right
`or(not(set.member(…)), eq(ite…))`. So the Rust and Lean symbolic compilers each DETERMINISTICALLY
build the disjunction in a different operand order — a real term-shape divergence (NOT "or stored in
indeterminate order"). Open question: genuine faithfulness bug to fix at the source, OR the assert
should normalize commutative ops. Capture + look at both compilers' disjunction construction.

## Hardening (working tree; in bootstrap-boost-lossless package)
- `cedar-drt/fuzz/src/symcc.rs`: added `asserts_match_result(rust, lean) -> Result<(),String>` — the
  non-panicking sibling of `assert_that_asserts_match` (returns the diff instead of `similar_asserts::assert_eq!`).
- `cedar-drt/coverage/src/target.rs` `SymccCheckTarget::run` (NeverErrors + AlwaysAllows/Denies): replaced
  `.unwrap().unwrap()` + `assert_that_asserts_match` with explicit match → push a violation string
  (lean compile-fail / encode-err / assert mismatch) and CONTINUE; return one aggregated
  `TargetResult::Violation` (capped MAX_V=8) or Ok. No panic → survives `panic=abort`; the collect
  harness's `on_violation` DUMPS the input (schema+policies) so it's reproducible.
- NOT YET hardened: `SymccCheckTwoPolicies::run` (target.rs ~340, implies/equivalent/disjoint targets)
  still uses `.unwrap()`/assert — harden the same way if those targets are run.

## Refined identification (2026-08-12, local probes + static analysis)
- **Crash 1 = a genuine Rust-accepts / Lean-rejects(tagNotFound) TYPECHECKER DISAGREEMENT (viol_166262
  family), NOT a mere generator gap.** KEY: Rust `CompiledPolicy::compile` runs Cedar's typechecker
  FIRST (`compiled_policies.rs:86 symcc::well_typed_policy(policy, env, schema)?`) — on an ill-typed
  policy it would Err and the harness's `let Ok(compiled)=… else continue` would SKIP it. Here it
  SUCCEEDED ⇒ Rust deems the policy well-typed for that req-env. The crash is the harness then
  `.unwrap()`-ing the LEAN side (`asserts_of_check_never_errors`), whose typechecker returns
  `Cedar.Validation.TypeError.tagNotFound` — an UNHANDLED disagreement (harness assumed Lean agrees
  since Rust did). So there is NO shared well-typedness gate; each side typechecks independently and
  the harness unwrapped the divergence.
  Reconciling with the errsmoke "17,600 agree" result: that used Lean's MULTI-ENV `validate`; the symcc
  path uses PER-req-env `well_typed_policy`, a different entry that can diverge (and its re-encode may
  trigger the record/tag order-sensitivity). Still need the captured policy to pin the exact mechanism
  (spurious Lean tagNotFound via ordering vs Rust-too-lenient). The ~0.5% welltyped soundness gap
  (UnsafeAttributeAccess 94/17600, both engines agree) is a SEPARATE real finding, not this crash.
- **Crash 2 is a DETERMINISTIC Lean-vs-Rust term divergence (NOT indeterminate `or` storage).** Both
  `or` factories preserve caller operand order (Rust `factory.rs:129` args=[t1,t2]; Lean
  `Factory.lean:92` `.app .or [t₁,t₂]`), so the flip (`or(eq…, not(set.member…))` vs
  `or(not(set.member…), eq…)`) comes from the two compilers PASSING the disjunction operands in
  opposite order (a `||` short-circuit / optional-error combine built differently). `assert_that_asserts_match`
  compares `BTreeSet<Term>` structurally (no commutative normalization) so it flags it. FIX options:
  (a) make both compilers order the disjunction identically, or (b) normalize commutative ops in the
  compare. Exact `||` site needs the minimized input.
- Reproduction is RARE (~1 per hour-long run): ~800k local (policy,req_env) checks (sz12 & sz20) hit
  NEITHER. Don't brute-force locally — rely on the hardened rerun's dumped violations. Repro bin left
  at `cedar-drt/coverage/src/bin/symcc_repro.rs` (replays a seed range through the never-errors check).
- Related: the ~0.5% welltyped soundness gap ties to [[welltyped-generator-soundness-bugs]].

## ⚠️ CORRECTION (2026-08-12 pm): crashes DID NOT REPRODUCE — do not call them confirmed bugs
Pinpointed both original aborts from the crashy run's SSM logs (cmd ba71908c on i-0ba0f229588eb59ca):
BOTH were in PHASE 1 (throughput probe), un-hardened `.unwrap()`/`assert!` under panic=abort →
"failed to initiate panic, aborting" (Lean-obj Drop-during-unwind double fault).
- Crash 1: `--single-rep 8 --seed-base 0 --seed-stride 1e9` ⇒ seed 8000000000, size 20. Lean
  tagNotFound compile-fail (target.rs:281). Many SLOW_SEED (50s) abandons first (8000044800…8000372600+);
  crash after those.
- Crash 2: `--single-rep 17` ⇒ seed 17000000000, size 12. Deterministic-looking Rust-vs-Lean `or`
  operand-order term diff (target.rs:283), crashed within the ~2000-input warmup (very early).
`symcc_repro.rs` defaults (8e9/sz20, 17e9/sz12) already match these exact seeds.

EVIDENCE THEY'RE RARE/NON-REPRODUCING:
- HARDENED rerun i-0050c0d27f6bd83ff (S3ROOT ci-boost-lossless-symcc-20reps-3600s-v2) ran the FULL
  hour × 20 reps × 3 arms (~150M+ never-errors checks; fused wt-policy count-matched 1.00) → **0
  violations**. Phase-1 rep17 seed 17e9/sz12 alone did 4.7M valids, no abort.
- Local `symcc_repro 17000000000 12 200 mismatch` → 52,382 checks, 0 mismatches. (Earlier ~800k also 0.)
- Hardened instance generator is PURE BOOST (CedarGen.lean: 0 PolicyGenError imports; Generate.lean
  strategies = [budget-aware,steep,steep-tags,typeof-check,welltyped-policy]) — as the user required.

MECHANISM ANALYSIS (static, cedar/cedar-policy-symcc/src):
- Rust `compile_or` (compiler.rs:365) is DETERMINISTIC + operand-order-preserving → a plain `||` can't
  swap. `any_true`/`any_none`/`if_all_some` fold over `ts: impl IntoIterator` (factory.rs:799-808) —
  a nondeterminism source ONLY if fed a hash-ordered collection, but all callers (authorizer.rs:48,
  compiler.rs:396/417, compile_set) pass Vecs → deterministic. So Rust-side term construction looks
  DETERMINISTIC for a fixed policy.
- ⇒ If Rust is deterministic per-policy, crash-2's non-reproduction on the SAME seed means the crashy
  run's GENERATOR produced a DIFFERENT policy than the hardened rerun's (build/toolchain drift between
  the 13:xx crashy build and 18:37 hardened rebuild), NOT run-to-run term nondeterminism. UNCONFIRMED —
  couldn't locate a nondeterminism source, and couldn't diff the two generator builds (crashy instance
  stopped, can't SSM). Genuine compiler nondeterminism (e.g. a HashMap I didn't find) is not ruled out.
- DO NOT claim these are confirmed spec bugs. They are captured, real ABORTS, but the underlying
  divergence has NOT been reproduced on any current generator build.

RELIABLE REPRO PATH (needs user OK — costs $, MUST stop not terminate): start stopped crashy instance
i-0ba0f229588eb59ca (has the EXACT generator binary that aborted; generator is deterministic so seed
17e9/sz12 will regenerate the same policy), build+run the hardened `symcc_repro` there, capture the
offending policy, minimize. If it ALSO doesn't reproduce there → genuine nondeterminism.

## ★★ TRUE ROOT CAUSE (2026-08-12 night): NON-DETERMINISTIC PROTOBUF ENCODING (prost HashMap map fields)
FULLY PROVEN — supersedes the "transient throughput fault" guess below (that was wrong; and my
"not in the corpus" was ALSO wrong — I'd only searched 20 of 28,298 corpus files).
Chain (all verified on i-0ba0f229588eb59ca, crash build):
1. Full corpus search (all 28,298 rep-17 collect batch files, 48-way sharded, ~79M policy-checks) found
   the EXACT crash policy in `batch_004014.bin`: `forbid(...resource is b::id) when { ... {a: b::id::"owner".getTag("e") <= b::id::"owner".getTag("e"), bar: b::id::"owner".getTag("e")} has baz ... && !b::id::"owner".hasTag("e") }`;
   entity `b::id` has datetime-typed tags. (Earlier "not in corpus" was from checking only 20 files — WRONG.)
2. Running the Rust-vs-Lean never-errors compare on THAT policy across 240 fresh processes: 107/240
   MISMATCH (~45%). So it IS reproducible — nondeterministically.
3. Which side? Rust full-term hash = 240/240 IDENTICAL (deterministic). A captured mismatch shows
   LEAN=`or(eq(datetimeGuard), not(hasTagGuard))`, RUST=`or(not, eq)`. ⇒ LEAN side flips.
4. Lean compile has NO hashmap (only Wildcard.lean; ifAllSome/anyNone fold a List in order). Rust
   `ExprKind::Record` = `Arc<BTreeMap>` (sorted). So neither compiler is the source.
5. THE SOURCE: cedar proto schema encodes record/attrs/tags/context as `map<string,Expr>`
   (cedar/cedar-policy/protobuf_schema/core.proto:24,284,290,292). cedar-policy/build.rs calls
   `prost_build::compile_protos` with NO `.btree_map()` ⇒ prost generates those as `std::HashMap`.
   Encoding a HashMap iterates in per-process RandomState order ⇒ NON-DETERMINISTIC wire bytes.
6. PROOF: re-encoding the same PolicySet (`ps.encode()`) in 240 fresh processes → 8 DISTINCT byte
   orderings, all identical length 149165. Rust's own compile uses the in-memory BTreeMap (unaffected,
   240/240). Lean keeps wire order (Proto.Map = Array) and folds anyNone in that order ⇒ its error-guard
   `or` operands swap ⇒ structural DRT mismatch vs Rust's fixed order. `or` is commutative so it's
   semantically equivalent, BUT a non-deterministic verifier/serializer IS a real bug (user: "no such
   thing as DRT flakiness, if it's a possible bug it's a bug").
FIX: add `.btree_map(["."])` to the prost_build config in cedar-policy/build.rs (all proto map fields →
BTreeMap → deterministic sorted encoding). Defensive add-on: Lean compileRecord could sort `ats` by attr.

★ SAME BUG AS THE "hasTag/tagNotFound" FINDING [[drt-mismatch-tagnotfound-record-projection]] (viol_166262,
already root-caused 2026-08-09). Identical two-bug structure:
  - BUG 1 (shared): cedar `Protobuf::encode` nondeterministic (prost HashMap map fields). Fix: btree_map
    in cedar/cedar-policy/build.rs (UPSTREAM cedar).
  - BUG 2 (the Lean order-sensitivity): Lean `Expr.record = List (Attr × Expr)` (Spec/Expr.lean:70) is
    decoded from proto in WIRE ORDER without sorting, whereas Rust `Expr::Record = Arc<BTreeMap>` is sorted/
    canonical. So an order-sensitive Lean consumer diverges: the VALIDATOR's capability-equality on a
    record-projection receiver (`(x,.tag t) ∈ c`, Typechecker.lean getTag) → spurious tagNotFound (WRONG
    VERDICT, correctness bug); the SYMCC compiler's `compileRecord`/`anyNone` fold → commutative `or` swap
    (benign, semantically equal). Two symptoms, one cause.
  - THE UNIFYING FIX (resolves BOTH): canonicalize `Expr.record` attrs (sort by key) on CedarProto decode
    to match Rust's BTreeMap. Then validation is order-invariant AND symcc terms are deterministic.
  - Minimal validator repro already saved: .experiment_holding/mismatch_viol_166262/MINIMAL_{schema,policy}
    + vr_{good,bad}.bin. My symcc repro: batch_004014 policy (b::id datetime-tag record projection).
This is a cedar/cedar-spec (upstream) bug, not our generator changes.

★ CRASH 1 FINISHED (2026-08-13) = LITERALLY the same viol_166262 policy, confirmed order-sensitive.
Full 48-way-sharded scan of the rep-8/sz20 symcc collect corpus (881 files, partitioned disjointly) →
exactly 1 Lean tagNotFound compile-fail, in batch_000166. Its policy is IDENTICAL to viol_166262:
`forbid(principal in e::e::id::"d", action == Action::"d", resource) when { !(datetime<=…) &&
(({b: resource, d: (resource.hasTag("owner"))||true}.b).hasTag("owner")) &&
(({b: resource, d: …}.b).getTag("owner")) && … }` — the record-projection getTag("owner") on e::e::id.
FLIP TEST (240 fresh processes on batch_000166): 129/240 tagNotFound, 111/240 OK (~54% flip). ⇒ crash 1's
tagNotFound is ORDER-SENSITIVE (nondeterministic-encode × order-sensitive Lean typecheck), NOT a
deterministic reject. So crash 1 = the hasTag/tagNotFound bug via symcc's well_typed_policy gate; crash 2
= same root cause via the symcc term compare (benign commutative or-swap). Both symcc crashes + the
validation tagNotFound are ONE bug. Fix = canonicalize Expr.record attrs (sort by key) on CedarProto
decode (+ .btree_map in cedar build.rs for encode reproducibility). symcc_repro modes added: sig:<needle>, types, types-worker,
corpus <dir>, corpus-sig <dir> <needle>, encmd5 <dir>. Full 12GB rep-17 corpus was synced to /mnt/rep17full.

## (SUPERSEDED GUESS) crashes are THROUGHPUT-PROBE TRANSIENT FAULTS, not spec bugs
Definitive investigation on the restarted crashy instance i-0ba0f229588eb59ca (stopped again after):
- Both aborts were in PHASE 1 throughput probe. Full crash-2 diff = ONE commutative `or` with operands
  SWAPPED (`or(eq(datetimeGetTag<=self), not(hasTag))` vs `or(not(hasTag), eq(...))`) — everything else
  byte-identical. `or` is commutative ⇒ semantically EQUIVALENT; the DRT compares `BTreeSet<Term>`
  structurally (no commutative normalize) so it flags the swap. NOT a soundness bug.
- REPRODUCTION: does NOT reproduce. (a) Identical original binary replay of seed 17e9/sz12 → 199k valids
  EXIT 0. (b) 60 single + 30 parallel fresh processes → 0. (c) symcc_repro mismatch scan of the exact
  seed-17e9 stream (5000 batches, 1.4M checks) → 0. (d) symcc_repro `corpus` mode replaying the ACTUAL
  rep-17 COLLECT CORPUS from S3 (ci-boost-lossless-symcc-20reps-3600s/symcc-wt-policy-sz12/rep_17/corpus,
  52k checks) → 0 mismatches, 0 compile-fails.
- WHY it can't be a policy bug: generator is deterministic (two symcc_repro runs → identical batch 30
  pidx 95); Rust symcc term build is deterministic (env.rs/enforcer.rs/symbolizer.rs all BTreeMap/BTreeSet,
  `enforce`→BTreeSet<Term>, NO HashMap); the collect corpus on the SAME seed has NO mismatching policy.
  So no reproducible offending policy EXISTS in the deterministic stream.
- ROOT CAUSE (leading, evidence-backed): throughput generates via `timeout_ffi.rs` — a worker thread that,
  on a slow seed, is ABANDONED and left running its Lean computation concurrently with fresh workers +
  the main thread's symcc Lean FFI calls, under 191-way memory pressure. Transient Lean-runtime/FFI heap
  corruption → garbled term (crash2) / spurious tagNotFound (crash1) + the `failed to initiate panic,
  aborting` DOUBLE-FAULT. Crash-1 rep had 2 SLOW_SEED abandonments; crash-2 ran beside 190 siblings.
  The COLLECT path (generator.generate then target.run, same thread, sequential, no timeout wrapper) is
  clean — matches hardened 20-rep rerun: 0 violations. symcc_repro corpus/sig/types modes live on the
  instance's built binary (rebuild from src if instance re-terminated: cargo build --release --features symcc --bin symcc_repro).
- FOLLOW-UPS if ever revisited: (1) throughput probe shouldn't run the DRT target (measure gen rate only),
  or serialize FFI; (2) fix leaked-worker concurrency in timeout_ffi (join/kill instead of leak); (3) if
  keeping the symcc term DRT, normalize commutative ops (or/and) before the BTreeSet compare.
- `symcc_repro` gained modes: `sig:<needle>` (find policy whose Rust term contains needle), `types`
  (dump per-batch request-env types), `corpus <dir>` (replay a collected corpus through the compare).

## Status / next
- S3 UPLOADER BACKOFF FIX DONE (s3.rs put_with_retry, 12 attempts exp backoff; BatchUploader+
  StreamingUploader count only on success, loud FATAL on exhaustion; added tokio "time" feature).
  Builds clean. This is the guided count-match fix ([[guided-drain-loss-and-mapping]]).
- AWS S3 access from experiment instances: use the INSTANCE ROLE (cedar-exp-runner), i.e. `unset
  AWS_PROFILE` — the CLI has no `cedar-experiment` profile (that's only for the experiment binary's
  credential_process). My local machine uses AWS_PROFILE=cedar-experiment; the instances do not.
- Validation boost-lossless rerun (i-03809cda0252803c3) unaffected (validation-drt collects via
  run_val_test_checked).
