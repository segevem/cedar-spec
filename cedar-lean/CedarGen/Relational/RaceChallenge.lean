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

import CedarGen.Relational.SpecimenTacticDemo

/-! # Shared challenge for the specimen-vs-manual disproving race

Reuses the `fooBar` schema (`entity E { foo: Bool, bar: Bool }; action a`),
`fooBarEnv`, `eFooP`/`eBarR`, and all generator boilerplate from
`SpecimenTacticDemo`.

Two policies:
* `policyOrs`      — `permit when { principal.foo || resource.bar }`
* `policyTwoWhens` — `permit when { principal.foo } when { resource.bar }`

`raceThm` claims they are equivalent on all well-typed inputs. It is FALSE:
multiple `when` clauses *conjoin*, so `policyTwoWhens` is `foo && bar`, whereas
`policyOrs` is `foo || bar`. The task is to disprove `raceThm`. -/

open CedarGen.Relational.ReqEnt
open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-- `permit(...) when { principal.foo || resource.bar };` -/
def policyOrs : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, .or eFooP eBarR⟩]⟩]

/-- `permit(...) when { principal.foo } when { resource.bar };`
    (two `when` clauses — they conjoin, i.e. `foo && bar`). -/
def policyTwoWhens : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, eFooP⟩, ⟨.when, eBarR⟩]⟩]

/-- The (false) claim to disprove: the two policies agree on every well-typed input. -/
def raceThm : Prop :=
  ∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    isAuthorized req es policyOrs = isAuthorized req es policyTwoWhens
