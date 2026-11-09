/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import CedarGenProof.ExprGen.EnumHasTypeRecord3.Stmts

/-! Every 8th part of the component `enum HasTypeRecord [3]`, from the 1th. Part of the proof described in `CedarGenProof.ExprGen`. -/

open Cedar.Validation.Relational Cedar.Validation.Relational.ExprGen.RequestVars

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option specimen.parallelProofs true
set_option specimen.completeDropUnreachable true
set_option specimen.reachSimpAll false
set_option basalt.walk.pruneDischarge false

#specimen_prove_slice enum HasTypeRecord [3] 1 of 8
