import CedarGen.Relational.PolicyGen
import CedarGen.Relational.SchemaTest
import Cedar.Validation

/-! # Soundness PBT (INERT — uncomment the `#eval` below to run).

    Pure-Lean soundness check with the REAL `validate`, categorizing rejections into
    `unknownEntity` (Bug 1 — undeclared `is` type), `attrNotFound` (Bug 2 — reqty↔acts
    context desync), and `other`/`impossiblePolicy` (Bug 3 — a Rust warning the DRT gate
    accepts, not a real rejection). All three are now resolved: latest run reports
    `ok=859  unknownEntity=0  attrNotFound=0  other=141` (the 141 = impossiblePolicy).
    Kept as a re-runnable regression harness; the `#eval` is left commented so building this
    module doesn't re-run the full validate loop. -/

open CedarGen.Relational.PolicyGen
open Cedar.Spec Cedar.Validation

-- Uncomment to re-run the soundness categorization over the generator output:
-- #eval runPolicySoundnessPBT

def runPolicySoundnessPBT : IO Unit := do
  let mut ok := 0
  let mut unknownEntity := 0
  let mut attrNotFound := 0
  let mut other := 0
  for seed in List.range 40 do
    match ← generateSchemaOnly seed 12 with
    | none => pure ()
    | some env =>
      let schema : Schema := { ets := env.ets, acts := env.acts }
      let policies ← generatePolicies env 12 25 (some (seed + 1))
      for p in policies do
        match validate [p] schema with
        | .ok _    => ok := ok + 1
        | .error e =>
          let s := s!"{repr e}"
          if (s.splitOn "unknownEntity").length > 1 then unknownEntity := unknownEntity + 1
          else if (s.splitOn "attrNotFound").length > 1 then attrNotFound := attrNotFound + 1
          else if (s.splitOn "impossiblePolicy").length > 1 then other := other + 1
          else do
            if (s.splitOn "unexpectedType").length > 1 then pure () else pure ()
            IO.eprintln s!"OTHER: {s}"
  let total := ok + unknownEntity + attrNotFound + other
  IO.println s!"\n=== validate on WellTypedPolicy output ({total} policies) ==="
  IO.println s!"    ok={ok}  unknownEntity(Bug1)={unknownEntity}  attrNotFound(Bug2)={attrNotFound}  other={other}"
