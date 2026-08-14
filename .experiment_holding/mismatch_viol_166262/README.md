# DRT validation mismatch — viol_166262 (Lean rejects, Rust accepts)

Found 2026-08-08 in the boosted-generator corpus run `ci-run-boost-validation-20reps-3600s`
(arm `wt-policy-sz20`, rep_08). **0 mismatches in the archived old-generator run** — surfaced by the
record/isEmpty weight boost (record×8/cons×6/isEmpty×10 in Variants/BudgetAware.lean).

## ✅ FINAL ROOT CAUSE (2026-08-09): false positive from encode-nondeterminism × order-sensitive Lean validate
NOT a Cedar spec-vs-Rust divergence. Two real bugs compound:
1. `cedar-policy` `Protobuf::encode(Schema/PolicySet)` is NONDETERMINISTIC (HashMap/HashSet field order):
   same schema → 12/12 distinct byte strings; entity-type order shuffles. `ffi.validate` re-encodes each call.
2. Lean validation is ORDER-SENSITIVE: fed a FIXED "bad-order" byte string it returns `tagNotFound` 10/10;
   a FIXED "good-order" byte string returns OK 10/10. Both 2065B, same logical ValidationRequest, only
   repeated-field order differs. So a valid policy spuriously fails to validate for some serialization orders.
Together → random spurious `tagNotFound` → this false-positive DRT mismatch. Rust is always consistent (pass).
Minimal deterministic repro: `vr_good.bin` (→ OK) and `vr_bad.bin` (→ tagNotFound) in this dir — feed to the
Lean `validate` FFI via `CedarLeanFfi::validate_request_bytes` (test method added on the instance).
Bug 2 is the correctness bug to fix (CedarProto Schema decode / tag-map / ancestor⇄descendant inversion —
make validation order-invariant); bug 1 (sort proto map/set fields) fixes DRT reproducibility.

## THE ORIGINAL DISAGREEMENT (as recorded — now explained by the above)
- **Rust `cedar-policy` validator: "no errors or warnings"  → ACCEPTS (valid).**
- **Lean spec (DiffTest engine): `errors: ["tagNotFound"]`  → REJECTS (spurious, order-dependent).**

## Reproduction metadata (validation-drt, welltyped-policy strategy)
- target: `validation-drt`   strategy: `welltyped-policy`
- index: 166262   base_seed: **8000166400**   prov_index: 62   size: 20   schema_size: 20
- Exact protobuf inputs (durable): `viol_166262.policies.bin`, `viol_166262.schema.bin` (this dir)
- Also in S3: `s3://__S3_BUCKET__/ci-run-boost-validation-20reps-3600s/wt-policy-sz20/rep_08/violations/`

## Policy (Cedar text)
```
forbid(principal in e::e::id::"d", action == Action::"d", resource) when {
  (!((if true then (datetime("9499-09-21T13:38:02.079+1709")) else false)
      <= (if false then (duration("01275377357821557689ms")) else (datetime("4200-01-14T02:38:35.525Z")))))
  && ((({b: resource, d: (resource.hasTag("owner")) || true}.b).hasTag("owner"))
     && ((({b: resource, d: (resource.hasTag("owner")) || true}.b).getTag("owner"))
        && (true
           && ((!((Action::"b" in Action::"b") && ((baz::baz::"d".hasTag("owner")) && true)))
              && ((!(if (Action::"e" is Action) then (a::b::"owner".hasTag("owner")) else true)) && true)))))
};
```
Resource type (via `action == Action::"d"`, resource_apply_spec) = `e::e::id`, which has `tags: Some(Bool(AnyBool))`.

## SCHEMA WELL-FORMEDNESS — verified clear of known generator gaps (2026-08-08)
Structural check of the schema debug dump:
- Enum entities `b` and `baz::foo::b` BOTH have empty `descendants` → no enum-with-hierarchy edge
  (the known enum-hierarchy generator gap does NOT apply here).
- Every action UID is `Action`-typed → no action-type soundness gap.
- Resource type `e::e::id` (via `action == Action::"d"`) declares `tags: Some(Bool)` — a valid tag decl.
  Tagless entities (`a::b` tags None) only appear under `hasTag` (well-typed → false), never `getTag`.
- BOTH engines got PAST schema loading: Lean's `tagNotFound` is a policy-level `TypeError` (not a schema
  error) and Rust returned a policy validation result — so neither rejected the schema.
⇒ Divergence is genuine POLICY typechecking on an ACCEPTED, pathology-free schema, not a schema-validity
   artifact. DEFINITIVE confirmation still worth doing: replay the .bin through the harness + run the schema
   through Cedar strict schema validation independently.

## Suspected root cause (to verify)
The `tagNotFound` almost certainly comes from the tag-capability pattern threaded through a **record
projection**:
```
( {b: resource, d: …}.b ).hasTag("owner")   &&   ( {b: resource, d: …}.b ).getTag("owner")
```
`{b: resource, …}.b` projects the field back to `resource`. The left conjunct `E.hasTag("owner")` should
add capability `(E, tag "owner")` so the right conjunct `E.getTag("owner")` is safe (E is the *same*
record-projection expression syntactically). Rust tracks that capability (→ no error); **Lean's `typeOf`
apparently does NOT recognize the capability when the receiver `E` is a record-projection expression → emits
`tagNotFound`.** So the divergence is capability tracking for `getTag` through a `{…}.field` receiver.
(Other tag sites in the policy — `baz::baz::"d"` has String tags, `a::b::"owner"` has `tags: None` — are
candidates too; the record-projection getTag is the most likely trigger given records were boosted.)

Whether the bug is in Lean's `typeOf` (too strict — losing the capability) or Rust's (too lenient) is TBD;
Cedar's capability design suggests the capability *should* carry, i.e. Lean is likely the one to fix.

## Also present in the policy (possible confounds)
- Heterogeneous literal-guard `if`: `if true then datetime(...) else false` (then=datetime, else=bool).
  Under the relational `iteTt` this is well-typed (guard `tt` ⇒ then-branch type, else ignored). Not the
  error source (Rust accepted), but a notable pattern the boosted generator emits.
- Enum entity types (`b`, `baz::foo::b`), deep action hierarchy.

## Next steps to root-cause
1. Replay the two `.bin` files through the DRT harness locally to reproduce Lean=tagNotFound / Rust=ok.
2. Minimize: strip conjuncts until only the `({…}.b).hasTag/getTag` pair remains; confirm it still diverges.
3. Locate the tag-capability rule in Lean `Cedar/Validation/` (`typeOfGetTag` / capability set) and check
   whether the capability key uses the receiver expression and whether record-projection receivers are handled.
