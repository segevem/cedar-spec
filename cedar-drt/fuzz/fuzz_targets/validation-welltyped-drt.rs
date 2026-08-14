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

use cedar_drt_inner::{fuzz_target, guided_log, validation_drt};
use libfuzzer_sys::Corpus;

// Type-directed, WELL-TYPED-ONLY guided fuzzing of (strict) validation.
//
// Returning `Corpus::Reject` for ill-typed inputs tells libFuzzer not to add them to
// the corpus, so the coverage-guided search keeps and mutates only well-typed seeds —
// steering exploration toward well-typed directions. Well-typed inputs still run the
// full Rust-vs-Lean differential test. The reject predicate (`validation_drt::is_well_typed`)
// is shared verbatim with the coverage experiment's `COLLECT_WELLTYPED_ONLY` gate, so the
// two agree exactly on which inputs are rejected.
fuzz_target!(|input: validation_drt::FuzzTargetInput<true, true>| -> Corpus {
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(guided_log::install_stats_at_exit);
    validation_drt::fuzz_target_welltyped(input)
});
