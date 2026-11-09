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

import CedarGenProof.ExprGen.EnumHasTypeRecord3.Slice0
import CedarGenProof.ExprGen.EnumHasTypeRecord3.Slice1
import CedarGenProof.ExprGen.EnumHasTypeRecord3.Slice2
import CedarGenProof.ExprGen.EnumHasTypeRecord3.Slice3
import CedarGenProof.ExprGen.EnumHasTypeRecord3.Slice4
import CedarGenProof.ExprGen.EnumHasTypeRecord3.Slice5
import CedarGenProof.ExprGen.EnumHasTypeRecord3.Slice6
import CedarGenProof.ExprGen.EnumHasTypeRecord3.Slice7

/-! The component `enum HasTypeRecord [3]`: the parts its slices leave (they need an earlier component's theorems, which this file imports), then its theorems. Part of the proof described in `CedarGenProof.ExprGen`. -/

open Cedar.Validation.Relational Cedar.Validation.Relational.ExprGen.RequestVars

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option specimen.parallelProofs true
set_option specimen.completeDropUnreachable true
set_option specimen.reachSimpAll false
set_option basalt.walk.pruneDischarge false

#specimen_prove_finish enum HasTypeRecord [3]
