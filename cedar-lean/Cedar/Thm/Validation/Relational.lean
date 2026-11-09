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

import Cedar.Thm.Validation.Relational.CapsCongr
import Cedar.Thm.Validation.Relational.Completeness
import Cedar.Thm.Validation.Relational.Entities
import Cedar.Thm.Validation.Relational.EnvironmentValidation
import Cedar.Thm.Validation.Relational.Flags
import Cedar.Thm.Validation.Relational.Level
import Cedar.Thm.Validation.Relational.Policy
import Cedar.Thm.Validation.Relational.Request
import Cedar.Thm.Validation.Relational.Soundness
import Cedar.Thm.Validation.Relational.WellFormed
import Cedar.Thm.Validation.Relational.WfTypeEnv

/-!
This file collects the proofs that the relational specification of the validator
(`Cedar/Validation/Relational/`) agrees with the executable validator:

* typing: `hasType_iff_typeOf_ok` (`HasType` and `typeOf`);
* policy validation: `validate_iff` (`ValidPolicy` and `validate`);
* level-based validation: `validateWithLevel_iff` (`ValidPolicyAtLevel` and
  `validateWithLevel`);
* schema well-formedness: `typeEnvWF_iff_validateWellFormed` and
  `schemaWF_iff_validateWellFormed` (`TypeEnvWF`/`SchemaWF` and `validateWellFormed`);
* request and entity validation: `validateRequest_iff` and `validateEntities_iff`.

The typing correspondence is for `HasType false false` and holds on environments satisfying
`EnvAssumptions`, which every well-formed environment does
(`envAssumptions_of_validateWellFormed`). The results are stated both under `EnvAssumptions`
and under `Schema.validateWellFormed` (the `_of_validateWellFormed` variants).

The flags of `HasType` (`Flags.lean`) strengthen it monotonically (`HasType.mono`); with both
set it guarantees declared entities and distinct record keys (`HasType.strict_syntax`), so a
policy typed by it in every environment passes `validate` (`validate_singleton_of_typedInEnvs`).
Conversely, `typeOf` on an expression with declared entities and distinct record keys is
witnessed by `HasType true true` (`typeOf_complete_strict`, `hasType_strict_iff_typeOf_ok`), and
the policies `validate` accepts with distinct record keys are exactly the `ValidPolicyStrict` ones
(`validate_and_distinct_iff_strict`).
-/
