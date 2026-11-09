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

import CedarGenProof.ExprGen.EnumHasTypeRecord3.Finish
import CedarGenProof.ExprGen.GenHasType26.Finish
import CedarGenProof.ExprGen.GenHasType6.Finish
import CedarGenProof.ExprGen.Sound

/-! # `CedarGen.Relational.ExprGen`'s derivation, proved sound and complete

Every generator, enumerator and checker the derivation emits is proved sound and complete, in files
Lake checks in parallel:

* `Sound`: every definition's soundness;
* `Small`: the enumerators' searches, and the completeness of every component but the three
  largest;
* for each of the three largest (`enum HasTypeRecord [3]`, `gen HasType [6]`,
  `gen HasType [2, 6]`), in a directory of its own: `Stmts`, its parts' statements; `Slice0` to
  `Slice7`, every eighth part each, a part a slice cannot prove (it needs an earlier large
  component's theorems) left out; and `Finish`, which proves the parts left out, importing the
  earlier components' `Finish`, then the component's theorems.

Each command checks that the laws it proves depend on no axiom but `propext`, `Classical.choice` and
`Quot.sound`, and the build fails otherwise. This module imports them all, and reports the laws of
every definition by kind. -/

#specimen_audit "RequestVars"
