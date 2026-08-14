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

use cedar_drt::{
    logger::{TOTAL_MSG, initialize_log},
    tests::run_val_test,
};

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{PolicySet, Schema, SchemaFragment, ValidationMode, Validator};

use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, policy::GeneratedPolicy, schema,
    schema_gen::SchemaGen, settings::ABACSettings,
};
use cedar_testing::cedar_test_impl::time_function;
use libfuzzer_sys::Corpus;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::{debug, info};
use std::convert::TryFrom;

/// Input for validation DRT fuzz targets.
///
/// `SLOTS` controls whether generated policies may be templates with slots (`true`, the
/// standard behavior via `arbitrary_policy`) or are restricted to slot-free static policies
/// (`false`, via `arbitrary_static_policy`). Everything downstream is identical — the
/// static case is just wrapped back into an `ABACPolicy` so the target code path is unchanged.
#[derive(Debug, Clone)]
pub struct FuzzTargetInput<const TYPE_DIRECTED: bool, const SLOTS: bool> {
    /// generated schema
    pub schema: schema::Schema,
    /// generated policy
    pub policy: ABACPolicy,
}

impl<const TYPE_DIRECTED: bool, const SLOTS: bool> FuzzTargetInput<TYPE_DIRECTED, SLOTS> {
    pub const fn settings() -> ABACSettings {
        ABACSettings {
            enable_additional_attributes: true,
            ..if TYPE_DIRECTED {
                ABACSettings::type_directed()
            } else {
                ABACSettings::undirected()
            }
        }
    }
}

impl<'a, const TYPE_DIRECTED: bool, const SLOTS: bool> Arbitrary<'a>
    for FuzzTargetInput<TYPE_DIRECTED, SLOTS>
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: schema::Schema = schema::Schema::arbitrary(Self::settings(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = if SLOTS {
            schema.arbitrary_policy(&hierarchy, u)?
        } else {
            // Slot-free: generate a static policy and re-wrap it as an `ABACPolicy` so the
            // rest of the target is identical to the slots-on path.
            let static_policy = schema.arbitrary_static_policy(&hierarchy, u)?;
            ABACPolicy(GeneratedPolicy::Static(static_policy.0))
        };
        Ok(Self { schema, policy })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_policy_size_hint(&Self::settings(), depth),
        ]))
    }
}

#[cfg(test)]
mod slots_refactor_test {
    use super::*;

    fn count_slotted<const SLOTS: bool>() -> (u32, u32) {
        let (mut with, mut total) = (0u32, 0u32);
        for seed in 0..3000u64 {
            let mut bytes = [0u8; 4096];
            let mut st = seed.wrapping_mul(2654435761).wrapping_add(0x9e37);
            for b in bytes.iter_mut() {
                st ^= st << 13;
                st ^= st >> 7;
                st ^= st << 17;
                *b = (st & 0xff) as u8;
            }
            let mut u = Unstructured::new(&bytes);
            if let Ok(inp) = FuzzTargetInput::<true, SLOTS>::arbitrary(&mut u) {
                total += 1;
                let ps = inp.policy.into_policy_set();
                if ps.templates().any(|t| t.slots().count() > 0) {
                    with += 1;
                }
            }
        }
        (with, total)
    }

    #[test]
    fn slots_off_is_slot_free() {
        let (off, off_t) = count_slotted::<false>();
        let (on, on_t) = count_slotted::<true>();
        eprintln!("SLOTS=false: {off}/{off_t} slotted;  SLOTS=true: {on}/{on_t} slotted");
        assert_eq!(off, 0, "SLOTS=false produced {off} slotted policies — refactor broken");
    }
}

/// Smoke test for the `validation-welltyped-drt-noslots` target: the well-typed reject gate
/// (`fuzz_target_welltyped`) must emit ONLY validated terms. We reproduce exactly what the
/// target does — keep an input iff `is_well_typed`, then log it via `encode_replayable` — and
/// verify every KEPT input still passes the Rust strict validator AFTER the proto
/// encode→decode roundtrip the corpus/replay uses (catching both gate bugs and roundtrip
/// leaks), and that no kept policy carries a slot.
#[cfg(test)]
mod welltyped_gate_test {
    use super::*;
    use cedar_policy::proto::traits::Protobuf;

    #[test]
    fn noslots_gate_emits_only_validated_terms() {
        let (mut generated, mut kept, mut revalidated) = (0u32, 0u32, 0u32);
        for seed in 0..4000u64 {
            let mut bytes = [0u8; 4096];
            let mut st = seed.wrapping_mul(2654435761).wrapping_add(0x9e37);
            for b in bytes.iter_mut() {
                st ^= st << 13; st ^= st >> 7; st ^= st << 17;
                *b = (st & 0xff) as u8;
            }
            let mut u = Unstructured::new(&bytes);
            let Ok(inp) = FuzzTargetInput::<true, false>::arbitrary(&mut u) else { continue };
            generated += 1;
            let Ok(schema) = Schema::try_from(inp.schema.clone()) else { continue };
            let ps = inp.policy.into_policy_set();
            // The gate: only well-typed inputs are Kept + logged (everything else Rejected).
            if !is_well_typed(&schema, &ps) { continue; }
            kept += 1;
            // No slot may survive the SLOTS=false path.
            assert_eq!(
                ps.templates().filter(|t| t.slots().count() > 0).count(), 0,
                "kept a slotted policy on the noslots path"
            );
            // Roundtrip through the EXACT framing the corpus uses, then re-validate.
            let framed = encode_replayable(&schema, &ps);
            let slen = u32::from_le_bytes([framed[0], framed[1], framed[2], framed[3]]) as usize;
            let schema2 = Schema::decode(&framed[4..4 + slen]).expect("decode schema");
            let ps2 = PolicySet::decode(&framed[4 + slen..]).expect("decode policies");
            assert!(
                is_well_typed(&schema2, &ps2),
                "a KEPT input failed strict validation after roundtrip — the gate/roundtrip \
                 leaked an ill-typed term (seed {seed})"
            );
            revalidated += 1;
        }
        eprintln!(
            "welltyped-noslots gate: generated={generated} kept(well-typed)={kept} \
             revalidated_after_roundtrip={revalidated}"
        );
        assert!(kept > 0, "no well-typed inputs kept in 4000 seeds — generator/gate broken");
        assert_eq!(kept, revalidated, "some kept inputs failed re-validation after roundtrip");
    }
}

/// Well-typedness predicate SHARED with the coverage experiment's reject gate
/// (`cedar_drt_coverage::target::is_well_typed`): an input is "well-typed" iff the
/// Rust strict validator accepts it with **no errors**. The `validation-welltyped-drt`
/// guided target and the experiment collect MUST use the identical definition so that
/// "if the corpus rejects it, we reject it too" holds exactly.
pub fn is_well_typed(schema: &Schema, policies: &PolicySet) -> bool {
    Validator::new(schema.clone())
        .validate(policies, ValidationMode::Strict)
        .validation_passed()
}

/// Encode `(schema, policies)` as `[schema_len:u32-le ‖ schema-proto ‖ policies-proto]`
/// — the SAME framing the collect corpus uses — so the coverage experiment can replay
/// a guided run's full valid-input stream through the instrument-coverage binary.
pub fn encode_replayable(schema: &Schema, policies: &PolicySet) -> Vec<u8> {
    use cedar_policy::proto::traits::Protobuf;
    let schema_bytes = schema.encode();
    let policy_bytes = policies.encode();
    let mut out = Vec::with_capacity(4 + schema_bytes.len() + policy_bytes.len());
    out.extend_from_slice(&(schema_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(&schema_bytes);
    out.extend_from_slice(&policy_bytes);
    out
}

/// Like [`fuzz_target`], but returns a [`Corpus`] verdict so libFuzzer only keeps —
/// and mutates from — WELL-TYPED inputs, steering the coverage-guided search toward
/// well-typed directions. Ill-typed inputs (schema conversion failure, or a policy the
/// Rust validator rejects) return [`Corpus::Reject`]: libFuzzer does not add them to the
/// corpus and won't use them to guide future mutation. Well-typed inputs still run the
/// full Rust-vs-Lean DRT comparison — a mismatch on a well-typed input is still a bug.
pub fn fuzz_target_welltyped<const TYPE_DIRECTED: bool, const SLOTS: bool>(
    input: FuzzTargetInput<TYPE_DIRECTED, SLOTS>,
) -> Corpus {
    initialize_log();
    crate::guided_log::note_attempt();
    let def_impl = CedarLeanFfi::new();

    let Ok(schema) = Schema::try_from(input.schema.clone()) else {
        return Corpus::Reject;
    };
    let policyset = input.policy.into_policy_set();
    // Reject ill-typed inputs — keep only what the Rust strict validator accepts.
    if !is_well_typed(&schema, &policyset) {
        return Corpus::Reject;
    }
    // Kept (well-typed): log the replayable input for the coverage experiment.
    crate::guided_log::log_input(&encode_replayable(&schema, &policyset));
    debug!("Well-typed schema: {schema:?}");
    debug!("Policies: {policyset}");
    let (_, total_dur) =
        time_function(|| run_val_test(&def_impl, schema, &policyset, ValidationMode::Strict));
    info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
    Corpus::Keep
}

pub fn fuzz_target<const TYPE_DIRECTED: bool, const SLOTS: bool>(
    input: FuzzTargetInput<TYPE_DIRECTED, SLOTS>,
) {
    initialize_log();
    crate::guided_log::note_attempt();
    let def_impl = CedarLeanFfi::new();

    // generate a schema
    if let Ok(schema) = Schema::try_from(input.schema.clone()) {
        debug!("Schema: {:?}", schema);

        // generate a policy
        let policyset = input.policy.into_policy_set();
        debug!("Policies: {policyset}");

        // Log the replayable input (all valid inputs, not libFuzzer's minimized corpus)
        // for the coverage experiment's guided-collection drain.
        crate::guided_log::log_input(&encode_replayable(&schema, &policyset));

        // run the policy through both validators and compare the result
        let (_, total_dur) =
            time_function(|| run_val_test(&def_impl, schema, &policyset, ValidationMode::Strict));
        info!("{}{}", TOTAL_MSG, total_dur.as_nanos());

        // Dump test case if requested (simple dump without integration test framework)
        if let Ok(test_name) = std::env::var("DUMP_TEST_NAME") {
            let dump_dir = std::env::var("DUMP_TEST_DIR").unwrap_or_else(|_| ".".to_string());
            
            // Create directory if needed
            std::fs::create_dir_all(&dump_dir).ok();
            
            // Write schema
            if let Ok(schema_fragment) = SchemaFragment::try_from(input.schema) {
                if let Ok(schema_text) = schema_fragment.to_cedarschema() {
                    std::fs::write(
                        format!("{}/{}.cedarschema", dump_dir, test_name),
                        schema_text
                    ).ok();
                }
            }
            
            // Write policy
            std::fs::write(
                format!("{}/{}.cedar", dump_dir, test_name),
                policyset.to_string()
            ).ok();
        }
    }
}
