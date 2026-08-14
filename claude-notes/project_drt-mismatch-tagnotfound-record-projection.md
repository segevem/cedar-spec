---
name: drt-mismatch-tagnotfound-record-projection
description: "ROOT-CAUSED false-positive DRT mismatch (viol_166262): nondeterministic Schema Protobuf::encode (HashMap order) + order-SENSITIVE Lean validation → spurious tagNotFound on a valid policy; NOT a real spec-vs-Rust divergence"
metadata:
  node_type: memory
  type: project
  originSessionId: 80b33588-72ac-4fb9-a607-0ff17df90158
  modified: 2026-08-10T15:53:45.128Z
---

# DRT mismatch viol_166262 — Lean `tagNotFound` vs Rust accepts (2026-08-08)

**A genuine Lean-spec vs Rust-production validation divergence**, surfaced by the boosted welltyped
generator (record×8/cons×6/isEmpty×10 in `Variants/BudgetAware.lean`) — **0 mismatches in the archived
old-generator runs**, so the record boost found it. See [[generator-weight-tuning]].

## The disagreement
- Rust `cedar-policy` validator: **"no errors or warnings" → ACCEPTS**.
- Lean spec (DiffTest engine): **`errors: ["tagNotFound"]` → REJECTS**.

## Where it lives (durable)
- Full record + analysis: `cedar-spec/.experiment_holding/mismatch_viol_166262/` (README.md, full_message.txt,
  viol_166262.json, and the exact protobuf inputs .policies.bin / .schema.bin).
- S3: `s3://__S3_BUCKET__/ci-run-boost-validation-20reps-3600s/wt-policy-sz20/rep_08/violations/`
- Repro metadata: target `validation-drt`, strategy `welltyped-policy`, base_seed **8000166400**,
  index 166262, prov_index 62, size/schema_size 20.

## Schema well-formedness — verified clear of known gaps (2026-08-08)
NOT one of the known generator-gap schemas: enum entities (`b`, `baz::foo::b`) have EMPTY descendants
(no enum-hierarchy edge → [[enum-hierarchy-drt-mismatch]] doesn't apply); all action UIDs are `Action`-typed
(no action-type gap); resource `e::e::id` has valid `tags: Some(Bool)`; tagless entities appear only under
`hasTag`, never `getTag`. Both engines loaded the schema and reached POLICY typechecking (Lean `tagNotFound`
is a policy TypeError, not a schema error; Rust returned a policy result). ⇒ divergence is real policy
typechecking on an accepted, pathology-free schema. Definitive confirmation TODO: independent Cedar strict
schema-validation + harness replay of the .bin.

## Suspected root cause (UNVERIFIED)
The policy guards a tag read with a matching `hasTag` on the SAME expression, but the receiver is a
**record projection**:
`({b: resource, d: …}.b).hasTag("owner")  &&  ({b: resource, d: …}.b).getTag("owner")`.
`{b: resource,…}.b` = resource (entity `e::e::id`, which has `tags: Some(Bool)`). The `hasTag` should add
capability `(E, tag "owner")` making the `getTag` on the same expression `E` safe. Rust tracks it (accepts);
**Lean `typeOf` seemingly does NOT carry the tag capability when the receiver is a `{…}.field` expression →
`tagNotFound`.** Likely a Lean `typeOf`/capability bug (capability *should* carry per Cedar design), but
could be Rust too-lenient. TBD.

## ⚠️ DID NOT REPRODUCE from the dumped .bin (2026-08-08)
Built `cedar-drt/coverage/src/bin/repro_viol.rs` (reads schema.bin+policies.bin, `Schema/PolicySet::decode`,
calls `cedar_drt::tests::run_val_test_checked(&ffi, schema, &ps, ValidationMode::Strict)` — the SAME call
`coverage/src/target.rs:119` uses) and ran it ON THE ORIGINAL INSTANCE (i-0c3b846e672ce271d). Result:
**NO MISMATCH — engines AGREE.** Policy text round-trips identically. So the mismatch is not reproducible
from the saved proto. Candidate explanations (unresolved):
1. **Dump not faithful**: dump is `input.schema.encode()`; if `decode(encode(schema))` differs from the
   in-memory schema the harness validated (schema-proto round-trip not idempotent), the repro input ≠ the
   mismatching input. Policy round-trips fine (text matches); the SCHEMA is the suspect (tag decls).
2. **Nondeterminism** in the FFI/validate path (only ran once — could be flaky).
3. Repro path subtly differs from collection path (but both call the same run_val_test_checked/Strict).
### RESOLVED: seed-regen ALSO does not reproduce → transient flake (2026-08-08)
Built `cedar-drt/coverage/src/bin/repro_gen.rs` (regenerates via `ffi.generate_schema_typeof_proto`
{seed, size 20, schema_size 20, strategy "welltyped-policy", count 100} — the SAME call
`lean_gen.rs::refill` uses; note it returns `Result`, use `.ok()`/`Ok(b)`, NOT `Option`). At seed
**8000166400** it found idx **62** = the EXACT policy (identical text) and `run_val_test_checked` returned
**NO MISMATCH**. So neither the .bin replay NOR the exact seed-regen reproduces the disagreement.
CONCLUSION: since Cedar validation is deterministic on (schema, policies), an input that won't reproduce the
mismatch in isolation means the recorded `tagNotFound` was **TRANSIENT** — NOT a real spec/impl typechecking
divergence. Most likely a flake or STATE-ACCUMULATION fault in the long-lived Lean FFI during the heavily-
parallel collection run (one CedarLeanFfi instance validates hundreds of thousands of policies in sequence;
a leaked/stale Lean runtime state or a rare object-lifetime issue under load could yield a spurious error).
The input (schema + policy) itself is well-formed and both engines agree on it. NOT a bug to chase on this
input. If transient FFI faults recur, investigate FFI state reuse / object lifetimes in the collection loop,
not the typechecker. repro_viol.rs + repro_gen.rs left on the instance (untracked) and repro_gen saved to
.experiment_holding for reuse.

## ✅ ROOT CAUSE (2026-08-09) — nondeterministic encode + order-sensitive Lean validate
Reproduced on instance i-0c3b846e672ce271d. Repro bins (untracked, on instance under
`cedar-drt/coverage/src/bin/`): repro_viol, repro_gen, repro_text, repro_order, repro_char, repro_encode.
KEY EVIDENCE (repro_encode: `schema.encode()`/`ps.encode()` + `ffi.validate` in a loop):
- **`Protobuf::encode` for Schema is NONDETERMINISTIC**: 12/12 distinct byte strings for the SAME schema
  (all 1433B); decode-back `entity_types()` order shuffles between calls. PolicySet::encode also varies (4/12).
  Rust `HashMap`/`HashSet` iteration order → unstable proto field order.
- `ffi.validate` RE-ENCODES the schema every call (`ValidationRequest::new(ps,schema,mode)` →
  `call_lean_ffi_takes_protobuf`), so Lean gets a differently-ordered schema each call.
- **Lean's result tracks the SCHEMA encoding, not the policy**: identical policy-bytes (hash 692d…) gave
  both OK and tagNotFound; only the schema byte-order differed. ⇒ **Lean validation is ORDER-SENSITIVE** and
  returns a spurious `tagNotFound` for some orderings of this valid schema (Rust is always consistent = pass).
CONCLUSION: false-positive mismatch = nondeterministic encode (bug 1) feeding order-sensitive Lean validate
(bug 2). NOT a Cedar spec-vs-Rust typechecking divergence, NOT memory unsafety (earlier guesses wrong).
The record-projection `getTag` + multi-entity tag/ancestor schema is what makes Lean order-sensitive here.

### OURS vs UPSTREAM: **UPSTREAM** (2026-08-09)
The decode+validator are NOT our changes: `git status` clean for CedarProto/Schema.lean, Cedar/Data/Map.lean,
Cedar/Validation/Typechecker.lean, Types.lean; blame → merged upstream PRs (#880/#732/#561); `main` has the
identical code (incl. `mergeMaps` with the `(·.1 == ·.1)` comparator). So this is an ORIGINAL cedar-spec bug;
our boosted generator only surfaced it. `tagNotFound` is emitted at Typechecker.lean:198-200 (getTag:
`env.ets.tags? ety` = `(ets.find? ety).map tags?`, then capability check `(x,.tag t) ∈ c`). find? is a linear
BEq scan (order-robust), so the order-sensitivity is in an unsorted decoded Map / capability structure feeding
this path — exact offending Map not yet pinned statically (toSchema DOES sort via mapOfArray/qsort; mergeMaps
likely only fires on multi-occurrence merge). NEXT to pin exactly: instrument the Lean decode to dump the
internal Schema/Expr/capability structures for vr_good vs vr_bad and diff (needs instance).

### ✅ MINIMAL COUNTEREXAMPLE (2026-08-09) — delta-debugged, self-contained
Files: `.experiment_holding/mismatch_viol_166262/MINIMAL_{schema.cedarschema,policy.cedar}`.
SCHEMA: `entity E tags Bool;  action d appliesTo { principal: [E], resource: [E] };`
POLICY: `forbid(principal, action == Action::"d", resource) when {
  (({b: resource, k: true}.b).hasTag("owner")) && (({b: resource, k: true}.b).getTag("owner")) };`
Method: parse policy text + schema, run `ffi.validate` 200× (each re-encodes with random map order); count tagNotFound.
- 2-field record `{b,k}.b`: rust PASS, Lean tagNotFound **101/200**. 1-field `{b}.b`: **0/200**. no-record
  `resource.getTag`: **0/200**. 3-field `{a,b,c}.b`: **146/200** (rate rises with arity).
TRIGGER (necessary+sufficient): `hasTag`/`getTag` on a field PROJECTED from a record literal with **≥2
attributes**. 1 attr or bare entity never triggers. ⇒ the order-sensitive structure is the RECORD TYPE's
≥2-entry attribute map (built in the policy's nondeterministically-encoded field order, unsorted); the
tag-capability check `(x,.tag t) ∈ c` on the typed record-projection expr is order-sensitive → spurious
tagNotFound. Fully explains the field arity → rate relationship. Repro bins on instance: repro_min, repro_min2.

### WHY RUST IS IMMUNE (reference-impl confirmation, 2026-08-09)
Rust uses the SAME capability design as Lean: `CapabilitySet(BTreeSet<Capability{on_expr, attribute_or_tag,
kind}>)` (validator/types/capability.rs); `hasTag` ADDS `Capability::new_borrowed_tag(arg1,arg2)`
(typecheck.rs:1510), `getTag` CHECKS `prior_capability.contains(new_borrowed_tag(arg1,arg2))` (:1557) —
i.e. keyed on the RECEIVER EXPRESSION, exactly like Lean's `(x,.tag t) ∈ c`. Rust is immune purely because
**`Expr::Record = Arc<BTreeMap<SmolStr,Expr>>`** (ast/expr.rs:163) is SORTED/canonical, so `{b,k}.b` and
`{k,b}.b` are the identical Expr — both occurrences always compare equal → capability matches. (Also keys on
`ExprShapeOnly` + BTreeSet.) ⇒ CONFIRMS the mechanism WITHOUT a live trace: identical capability scheme, and
the ONLY difference is record representation. LEAN `Expr.record = List (Attr × Expr)` (Spec/Expr.lean:70),
decoded in wire order without sorting → order-sensitive equality → the bug.
FIX: canonicalize `Expr.record` on proto decode (sort attrs by key) to match Rust's BTreeMap + the schema
path (mapOfArray/qsort). Then record-projection receiver exprs are order-independent and capabilities match.

### TWO REAL BUGS TO FILE (both UPSTREAM cedar-spec)
1. `cedar-policy` `Protobuf::encode` (Schema + PolicySet): serialize map/set fields in a STABLE (sorted)
   order. Nondeterministic encoding breaks DRT reproducibility (dumped .bin re-encodes differently) and any
   byte-level caching/dedup. Likely in cedar/cedar-policy proto encode of ValidatorSchema entity/action/attr/tag maps.
2. Lean validation (or CedarProto→Lean schema decode / ancestor⇄descendant inversion / tag-map build):
   result must be INVARIANT to schema serialization order. Currently some orderings → `tagNotFound` on a
   valid policy. Investigate `CedarProto/Schema*` decode + `Cedar/Validation` tag-capability handling.
### ✅✅ BUG 2 ISOLATED AIRTIGHT (2026-08-09)
Added TEST methods to cedar-lean-ffi/src/lean_ffi.rs (ON INSTANCE ONLY — ephemeral; re-add locally to reuse):
`validation_request_bytes(ps,schema,mode)->Vec<u8>` (encode a ValidationRequest ONCE) and
`validate_request_bytes(&[u8])->Result<ValidationResponse,FfiError>` (validate FIXED bytes, bypassing the
per-call re-encode; body = `OwnedLeanObject::new_array_from_buf(bytes)` → `call_lean_ffi_function(validate,·)`
→ deserialize like validate_timed). repro_isolate/repro_save bins search for a good+bad encoding, then
validate each FIXED byte string 10×:
- GOOD-order bytes (2065B): 10/10 `Ok(Ok(()))`.  BAD-order bytes (2065B): 10/10 `Ok(Error("tagNotFound"))`.
- Both 2065B, `bytes_equal=false` — SAME logical ValidationRequest, only repeated-field ORDER differs.
⇒ Lean validation is DETERMINISTIC per fixed input but ORDER-SENSITIVE: some serialization orderings of a
valid schema/policy yield a spurious `tagNotFound`. Minimal deterministic repro saved:
`.experiment_holding/mismatch_viol_166262/vr_{good,bad}.bin` (+ S3 debug/viol_166262.vr_{good,bad}.bin).
To debug bug 2: `validate_request_bytes(vr_bad.bin)` ⇒ tagNotFound every time; decode both to see which
field-order (entity types / attrs / tags / ancestors) flips it; fix in CedarProto Schema decode / tag-map /
ancestor⇄descendant inversion (Cedar/Validation tag-capability), making result order-invariant.

## Root-cause / fix steps
1. Replay the two .bin files through the DRT harness to reproduce (Lean tagNotFound / Rust ok).
2. Minimize to just the `({…}.b).hasTag/getTag` pair.
3. Inspect Lean `Cedar/Validation/` tag-capability rules (`typeOfGetTag`, capability key) — check record-
   projection receivers. Compare to Rust `cedar-policy-core` typechecker getTag capability handling.

NOTE also present (not the error source): heterogeneous literal-guard `if true then datetime else false`
(well-typed under relational `iteTt`); enum entity types; deep action hierarchy.
