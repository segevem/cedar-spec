/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#![no_main]
use cedar_drt_inner::{fuzz_target, guided_log, symcc};

// Well-typed reject-gated variant of `symcc-term-drt-never-errors`: `fuzz_never_errors_welltyped`
// returns `Corpus::Reject` for any input the Rust strict validator rejects (`is_well_typed`, the
// SAME predicate as the validation experiment), so libFuzzer keeps/mutates only well-typed —
// hence compilable — inputs, steering the guided search toward inputs that actually exercise the
// symbolic compiler. This is the fair, well-typed-only handwritten arm to compare against the
// specimen `welltyped-policy` generator (analogous to `validation-welltyped-drt-noslots`). SymCC
// operates on static policies by construction, so no slots variant is needed.
fuzz_target!(|input: symcc::SinglePolicyFuzzTargetInput<32>| -> libfuzzer_sys::Corpus {
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(guided_log::install_stats_at_exit);
    symcc::fuzz_never_errors_welltyped(input)
});
