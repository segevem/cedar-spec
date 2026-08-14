import CedarGen.Relational.TypeOfLeanBase

/-! # DefaultScore derive with the arbitrary-deriving trace ON (diagnostic). -/

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.textOutput 3
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option trace.plausible.deriving.arbitrary true

namespace Variant.DefaultTrace

set_option specimen.scoreType "Scoring.DefaultScore" in
set_option specimen.precomputeWeights true in
scoped derive_mutual
  generator (fun env c ty => ∃ x cout, HasType x c env ty cout)

end Variant.DefaultTrace
