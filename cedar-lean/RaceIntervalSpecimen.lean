import CedarGen.Relational.RaceChallenge3

open CedarGen.Relational.ReqEnt
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.richOutput false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 2, max := 10, tests := 40000)
  (∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities intervalEnv req es →
    isAuthorized req es policyOverlap = isAuthorized req es policyBuggy)
