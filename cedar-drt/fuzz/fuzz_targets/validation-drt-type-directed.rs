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

// Type-directed fuzzing of (strict) validation. This is the PLAIN guided baseline for
// the coverage experiment: with CEDAR_FUZZ_LOG_DIR set, `fuzz_target` logs every valid
// input for the guided-collection drain; `install_stats_at_exit` flushes CEDAR_FUZZ_STATS.
fuzz_target!(|input: validation_drt::FuzzTargetInput<true, true>| {
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(guided_log::install_stats_at_exit);
    validation_drt::fuzz_target(input);
});
