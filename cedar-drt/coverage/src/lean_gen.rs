use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{PolicySet, Schema};
use cedar_policy::proto::traits::Protobuf;

use crate::{ValidationGenerator, ValidationInput};

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
    ffi: CedarLeanFfi,
    schema: Schema,
    size: u32,
}

impl LeanTypeOfGenerator {
    pub fn new(size: u32) -> Self {
        let ffi = CedarLeanFfi::new();
        let schema = Schema::from_json_str(TEST_SCHEMA_JSON)
            .expect("failed to parse test schema");
        Self { ffi, schema, size }
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
        });

        let proto_bytes = self.ffi.generate_typeof_proto(&params).ok()?;
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
        })
    }
}

/// Generator that generates BOTH a random schema and well-typed expressions
/// from the relational specs (WfTypeEnv + HasType). Each call produces a
/// fresh schema, giving much broader validator coverage.
/// Size is chosen uniformly at random from [min_size, max_size] each call.
pub struct LeanSchemaTypeOfGenerator {
    ffi: CedarLeanFfi,
    min_size: u32,
    max_size: u32,
}

impl LeanSchemaTypeOfGenerator {
    pub fn new(size: u32) -> Self {
        let ffi = CedarLeanFfi::new();
        Self { ffi, min_size: size, max_size: size }
    }

    pub fn with_range(min_size: u32, max_size: u32) -> Self {
        let ffi = CedarLeanFfi::new();
        Self { ffi, min_size, max_size }
    }
}

impl ValidationGenerator for LeanSchemaTypeOfGenerator {
    fn name(&self) -> &str {
        "lean-schema-typeof"
    }

    fn generate(&self, _seed: u64) -> Option<ValidationInput> {
        let params = serde_json::json!({
            "min_size": self.min_size,
            "max_size": self.max_size,
            "count": 1,
        });

        let proto_bytes = self.ffi.generate_schema_typeof_proto(&params).ok()?;
        if proto_bytes.len() < 4 {
            return None;
        }

        // Decode: [4-byte schema length LE] [schema bytes] [policyset bytes]
        let schema_len = u32::from_le_bytes([
            proto_bytes[0], proto_bytes[1], proto_bytes[2], proto_bytes[3],
        ]) as usize;

        if proto_bytes.len() < 4 + schema_len {
            return None;
        }

        let schema_bytes = &proto_bytes[4..4 + schema_len];
        let policy_bytes = &proto_bytes[4 + schema_len..];

        let schema = Schema::decode(schema_bytes).ok()?;
        let policies = PolicySet::decode(policy_bytes).ok()?;
        if policies.is_empty() {
            return None;
        }

        Some(ValidationInput {
            schema,
            policies,
            raw_bytes: Some(proto_bytes),
        })
    }
}
