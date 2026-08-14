import CedarGen.Relational.TypeOfLean
import Specimen

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

set_option linter.unusedVariables false
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.textOutput 3
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

-- set_option specimen.scoreType "Scoring.BoundedGradedScore" in
-- #time derive_mutual
--   checker (fun c a b => @SetContains c a b)

set_option specimen.scoreType "Scoring.BoundedGradedScore" in
#time derive_mutual
  generator (fun ets acts => ∃ ety₁ ety₂, NotDescendentOf ets acts ety₁ ety₂)
