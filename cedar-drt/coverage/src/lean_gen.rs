use cedar_policy::{PolicySet, Schema};
use cedar_policy::proto::traits::Protobuf;

use crate::timeout_ffi::TimeoutFfi;
use crate::{GenProvenance, ValidationGenerator, ValidationInput};

/// The fixed Cedar schema corresponding to `testEnv` in TypeOfLeanTest.lean.
const TEST_SCHEMA_JSON: &str = r#"{
    "": {
        "entityTypes": {
            "User": {
                "memberOfTypes": ["Group"],
                "shape": {
                    "type": "Record",
                    "attributes": {
                        "name": { "type": "String" },
                        "age": { "type": "Long" },
                        "active": { "type": "Boolean" },
                        "email": { "type": "String", "required": false },
                        "manager": { "type": "Entity", "name": "User", "required": false }
                    }
                },
                "tags": { "type": "String" }
            },
            "Group": {
                "shape": {
                    "type": "Record",
                    "attributes": {
                        "name": { "type": "String" },
                        "public": { "type": "Boolean" }
                    }
                }
            },
            "Document": {
                "shape": {
                    "type": "Record",
                    "attributes": {
                        "owner": { "type": "Entity", "name": "User" },
                        "title": { "type": "String" },
                        "score": { "type": "Long", "required": false }
                    }
                },
                "tags": { "type": "Long" }
            }
        },
        "actions": {
            "view": {
                "appliesTo": {
                    "principalTypes": ["User"],
                    "resourceTypes": ["Document"],
                    "context": { "type": "Record", "attributes": {} }
                }
            },
            "edit": {
                "appliesTo": {
                    "principalTypes": ["User"],
                    "resourceTypes": ["Document"],
                    "context": {
                        "type": "Record",
                        "attributes": {
                            "ip": { "type": "String" },
                            "mfa": { "type": "Boolean" },
                            "level": { "type": "Long", "required": false }
                        }
                    }
                },
                "memberOf": [{"id": "view"}]
            }
        }
    }
}"#;

/// Generator that calls into the Lean FFI to produce well-typed expressions
/// from the relational HasType specification. Returns protobuf-encoded PolicySet
/// bytes which are decoded directly — no text round-trip.
pub struct LeanTypeOfGenerator {
    ffi: TimeoutFfi,
    schema: Schema,
    size: u32,
    strategy: String,
}

impl LeanTypeOfGenerator {
    pub fn new(size: u32) -> Self {
        Self::with_strategy(size, "budget-aware".to_string())
    }

    pub fn with_strategy(size: u32, strategy: String) -> Self {
        let ffi = TimeoutFfi::new();
        let schema = Schema::from_json_str(TEST_SCHEMA_JSON)
            .expect("failed to parse test schema");
        Self { ffi, schema, size, strategy }
    }
}

impl ValidationGenerator for LeanTypeOfGenerator {
    fn name(&self) -> &str {
        "lean-typeof"
    }

    fn generate(&self, seed: u64) -> Option<ValidationInput> {
        let params = serde_json::json!({
            "seed": seed,
            "size": self.size,
            "count": 1,
            "strategy": self.strategy,
            "deterministic": true,
        });

        let proto_bytes = self.ffi.generate_typeof_proto(&params)?;
        if proto_bytes.is_empty() {
            return None;
        }

        let policies = PolicySet::decode(proto_bytes.as_slice()).ok()?;
        if policies.is_empty() {
            return None;
        }

        Some(ValidationInput {
            schema: self.schema.clone(),
            policies,
            raw_bytes: Some(proto_bytes),
            provenance: Some(GenProvenance {
                base_seed: seed,
                index: 0,
                size: self.size,
                schema_size: 0,
                strategy: self.strategy.clone(),
            }),
        })
    }
}

/// Generator that generates BOTH a random schema and well-typed expressions
/// from the relational specs (WfTypeEnv + HasType).
///
/// Generating a well-formed schema is expensive, so each FFI call produces one
/// schema plus `policies_per_schema` well-typed policies against it. The batch
/// is cached and doled out one (schema, single policy) input per `generate()`
/// call; when exhausted, a fresh schema+batch is generated with the next seed.
///
/// Wire format from Lean (`generateSchemaTypeOfProto`):
///   [4-byte LE schema length][schema proto bytes]
///   [4-byte LE policy count]
///   repeated: [4-byte LE policyset length][policyset proto bytes]
pub struct LeanSchemaTypeOfGenerator {
    ffi: TimeoutFfi,
    size: u32,
    schema_size: u32,
    strategy: String,
    policies_per_schema: u32,
    cache: std::cell::RefCell<SchemaBatch>,
}

/// Cached schema + its decoded single-policy policysets, with a cursor.
#[derive(Default)]
struct SchemaBatch {
    schema: Option<Schema>,
    policysets: Vec<PolicySet>,
    idx: usize,
    next_seed: u64,
    /// Base seed handed to the FFI for the currently cached batch (for provenance).
    base_seed: u64,
}

impl LeanSchemaTypeOfGenerator {
    pub fn new(size: u32) -> Self {
        Self::with_policies_per_schema(size, 1000)
    }

    pub fn with_range(_min_size: u32, max_size: u32) -> Self {
        Self::with_policies_per_schema(max_size, 1000)
    }

    pub fn with_policies_per_schema(size: u32, policies_per_schema: u32) -> Self {
        Self::with_sizes(size, size, "budget-aware".to_string(), policies_per_schema)
    }

    /// Construct with independent fuel budgets for the schema and the terms,
    /// plus the Specimen strategy used for the term (HasType) generation.
    /// Starts from seed 0; use [`with_sizes_seeded`] to pick a start seed.
    pub fn with_sizes(schema_size: u32, term_size: u32, strategy: String, policies_per_schema: u32) -> Self {
        Self::with_sizes_seeded(schema_size, term_size, strategy, policies_per_schema, 0)
    }

    /// Like [`with_sizes`] but starts generation at `start_seed`. Distinct reps
    /// use distinct start seeds so their corpora are disjoint samples.
    pub fn with_sizes_seeded(
        schema_size: u32,
        term_size: u32,
        strategy: String,
        policies_per_schema: u32,
        start_seed: u64,
    ) -> Self {
        let ffi = TimeoutFfi::new();
        Self {
            ffi,
            size: term_size,
            schema_size,
            strategy,
            policies_per_schema,
            cache: std::cell::RefCell::new(SchemaBatch {
                next_seed: start_seed,
                ..SchemaBatch::default()
            }),
        }
    }

    /// Read a 4-byte LE length prefix at `pos`, returning (value, new_pos).
    fn read_u32(buf: &[u8], pos: usize) -> Option<(usize, usize)> {
        if pos + 4 > buf.len() {
            return None;
        }
        let v = u32::from_le_bytes([buf[pos], buf[pos + 1], buf[pos + 2], buf[pos + 3]]) as usize;
        Some((v, pos + 4))
    }

    /// Call Lean to generate a fresh schema + batch of policies, populating the cache.
    fn refill(&self, cache: &mut SchemaBatch) -> bool {
        let seed = cache.next_seed;
        let params = serde_json::json!({
            "seed": seed,
            "size": self.size,
            "schema_size": self.schema_size,
            "strategy": self.strategy,
            "count": self.policies_per_schema,
        });
        // Stride by `policies_per_schema` so consecutive batches use DISJOINT
        // expr-seed ranges. The FFI derives expr seeds `seed+1 .. seed+count`
        // from this base; advancing by only +1 made ranges overlap by count-1,
        // and since most generated policies are schema-independent (literals /
        // extension calls), identical expr-seeds produced identical policies
        // across batches — collapsing corpus uniqueness though each batch is
        // ~99% distinct. Striding by count makes batch k use `k*count+1 .. (k+1)*count`.
        cache.next_seed = seed.wrapping_add(self.policies_per_schema as u64);

        let buf = match self.ffi.generate_schema_typeof_proto(&params) {
            Some(b) if b.len() >= 4 => b,
            _ => return false,
        };

        // [schema len][schema][count][ (ps len)(ps) x count ]
        let (schema_len, pos) = match Self::read_u32(&buf, 0) {
            Some(x) => x,
            None => return false,
        };
        if pos + schema_len > buf.len() {
            return false;
        }
        let schema = match Schema::decode(&buf[pos..pos + schema_len]) {
            Ok(s) => s,
            Err(_) => return false,
        };
        let mut pos = pos + schema_len;

        let (count, np) = match Self::read_u32(&buf, pos) {
            Some(x) => x,
            None => return false,
        };
        pos = np;

        let mut policysets = Vec::with_capacity(count);
        for _ in 0..count {
            let (ps_len, np) = match Self::read_u32(&buf, pos) {
                Some(x) => x,
                None => break,
            };
            pos = np;
            if pos + ps_len > buf.len() {
                break;
            }
            if let Ok(ps) = PolicySet::decode(&buf[pos..pos + ps_len]) {
                if !ps.is_empty() {
                    policysets.push(ps);
                }
            }
            pos += ps_len;
        }

        if policysets.is_empty() {
            return false;
        }

        cache.schema = Some(schema);
        cache.policysets = policysets;
        cache.idx = 0;
        cache.base_seed = seed;
        true
    }
}

impl ValidationGenerator for LeanSchemaTypeOfGenerator {
    fn name(&self) -> &str {
        "lean-schema-typeof"
    }

    fn generate(&self, _seed: u64) -> Option<ValidationInput> {
        let mut cache = self.cache.borrow_mut();

        // Refill if empty or exhausted.
        if cache.idx >= cache.policysets.len() {
            if !self.refill(&mut cache) {
                return None;
            }
        }

        let idx = cache.idx;
        let schema = cache.schema.clone()?;
        let policies = cache.policysets[idx].clone();
        let base_seed = cache.base_seed;
        cache.idx += 1;

        Some(ValidationInput {
            schema,
            policies,
            raw_bytes: None,
            provenance: Some(GenProvenance {
                base_seed,
                index: idx,
                size: self.size,
                schema_size: self.schema_size,
                strategy: self.strategy.clone(),
            }),
        })
    }
}

#[cfg(test)]
mod welltyped_policy_smoke {
    use super::LeanSchemaTypeOfGenerator;
    use crate::ValidationGenerator;
    use cedar_policy::{ValidationMode, Validator};

    /// The `welltyped-policy` strategy should produce policies with real scope
    /// constraints that the RUST validator also accepts (they're per-env well-typed
    /// in Lean, and real scopes narrow multi-env applicability). Reports the rate.
    #[test]
    fn welltyped_policy_rust_accepts() {
        let generator =
            LeanSchemaTypeOfGenerator::with_sizes(20, 12, "welltyped-policy".to_string(), 20);
        let mut ok = 0usize;
        let mut total = 0usize;
        let mut with_real_scope = 0usize;
        for seed in 0..200u64 {
            if let Some(input) = generator.generate(seed) {
                total += 1;
                // Does any policy carry a non-trivial (non-`Any`) scope? (sanity: we're
                // actually exercising the new scope-constraint paths, not all-`Any`.)
                let text = input.policies.to_string();
                if text.contains(" == ") || text.contains(" in ") || text.contains(" is ") {
                    with_real_scope += 1;
                }
                if Validator::new(input.schema)
                    .validate(&input.policies, ValidationMode::Strict)
                    .validation_passed()
                {
                    ok += 1;
                }
            }
        }
        eprintln!(
            "welltyped-policy: {ok}/{total} Rust-well-typed, {with_real_scope}/{total} carry a real scope"
        );
        assert!(total > 0, "generator produced nothing");
    }
}
