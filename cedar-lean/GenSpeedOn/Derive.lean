import CedarGen.Relational.ExprGenWeights
import Specimen.Basalt

set_option maxHeartbeats 0

/-! Generator speed with Basalt emission on: the production expression
derivation (`CedarGen.Relational.ExprGen`) without its proofs, `specimen.emitBasalt := true`. -/

namespace Cedar.Validation.Relational.ExprGen
open Cedar.Spec Cedar.Data Cedar.Validation Scoring Schedules
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option maxRecDepth 100000
set_option specimen.prefixSearch true
namespace Speed
set_option specimen.sizeSplit false in
set_option specimen.deriveFloors false in
set_option specimen.plainBinds true in
set_option specimen.parallelCodegen true in
set_option specimen.reportPhaseTimers true in
set_option specimen.scoreType "Scoring.InversionAwareScore" in
set_option specimen.weightModifier "Cedar.Validation.Relational.ExprGen.favorRequestVars" in
set_option specimen.precomputeWeights true in
scoped derive_mutual
  generator (fun env c ty => ∃ x cout, HasType true true x c env ty cout)
end Speed
end Cedar.Validation.Relational.ExprGen

