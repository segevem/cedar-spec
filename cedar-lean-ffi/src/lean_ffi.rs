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

#![expect(
    dead_code,
    reason = "declares a broad array of FFI functions, some of which are not currently used in any fuzz targets but are declared for completeness"
)]

mod tpe;

use crate::datatypes::{
    AuthorizationResponse, AuthorizationResponseInner, Env, ResultDef, Term, TimedDef, TimedResult,
    TpeResponse, TpeResponseInner, ValidationResponse,
};
use crate::err::FfiError;
use crate::lean_object::{
    OwnedLeanObject, call_lean_ffi_function, call_lean_ffi_takes_obj_and_protobuf,
    call_lean_ffi_takes_obj_protobuf_and_string, call_lean_ffi_takes_protobuf,
};
use crate::messages::*;

use cedar_policy::{
    Entities, Expression, Policy, PolicySet, Request, RequestEnv, Schema, ValidationMode,
};
use lean_sys::{
    lean_dec, lean_dec_ref, lean_finalize_thread, lean_initialize_runtime_module_locked,
    lean_initialize_thread, lean_io_mark_end_initialization, lean_io_mk_world,
    lean_io_result_is_ok, lean_io_result_show_error, lean_object, lean_set_exit_on_panic,
};

use std::sync::Once;

mod test_implementation;

// Import and signal Rust to link the exported Lean FFI code (which are C functions at this point)
#[allow(clippy::duplicated_attributes)]
#[link(name = "Cedar_Cedar", kind = "static")]
#[link(name = "Cedar_Cedar_SymCC", kind = "static")]
#[link(name = "Cedar_Protobuf", kind = "static")]
#[link(name = "Cedar_CedarProto", kind = "static")]
#[link(name = "Cedar_CedarGen", kind = "static")]
#[link(name = "Cedar_CedarFFI", kind = "static")]
#[link(name = "specimen_Specimen", kind = "static")]
#[link(name = "plausible_Plausible", kind = "static")]
#[link(name = "proofwidgets_ProofWidgets", kind = "static")]
#[link(name = "batteries_Batteries", kind = "static")]
unsafe extern "C" {
    fn runCheckNeverErrors(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckNeverErrorsWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckNeverErrorsWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckAlwaysMatches(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckAlwaysMatchesWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckAlwaysMatchesWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckNeverMatches(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckNeverMatchesWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckNeverMatchesWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckAlwaysAllows(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckAlwaysAllowsWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckAlwaysAllowsWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckAlwaysDenies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckAlwaysDeniesWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckAlwaysDeniesWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckEquivalent(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckEquivalentWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckEquivalentWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckImplies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckImpliesWithCex(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckImpliesWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckDisjoint(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckDisjointWithCex(schema: *mut lean_object, req: *mut lean_object)
    -> *mut lean_object;
    fn runCheckDisjointWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckMatchesEquivalent(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckMatchesEquivalentWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckMatchesEquivalentWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckMatchesImplies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckMatchesImpliesWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckMatchesImpliesWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckMatchesDisjoint(schema: *mut lean_object, req: *mut lean_object)
    -> *mut lean_object;
    fn runCheckMatchesDisjointWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckMatchesDisjointWithCexGivenRawModel(
        schema: *mut lean_object,
        req: *mut lean_object,
        raw_model: *mut lean_object,
    ) -> *mut lean_object;

    fn printCheckNeverErrors(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckAlwaysMatches(schema: *mut lean_object, req: *mut lean_object)
    -> *mut lean_object;
    fn printCheckNeverMatches(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckAlwaysAllows(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckAlwaysDenies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckEquivalent(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckImplies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckDisjoint(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckMatchesEquivalent(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn printCheckMatchesImplies(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn printCheckMatchesDisjoint(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;

    fn smtLibOfCheckNeverErrors(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn smtLibOfCheckAlwaysMatches(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn smtLibOfCheckNeverMatches(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn smtLibOfCheckAlwaysAllows(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn smtLibOfCheckAlwaysDenies(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn smtLibOfCheckEquivalent(schema: *mut lean_object, req: *mut lean_object)
    -> *mut lean_object;
    fn smtLibOfCheckImplies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn smtLibOfCheckDisjoint(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn smtLibOfCheckMatchesEquivalent(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn smtLibOfCheckMatchesImplies(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn smtLibOfCheckMatchesDisjoint(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;

    fn isAuthorized(req: *mut lean_object) -> *mut lean_object;
    fn validate(req: *mut lean_object) -> *mut lean_object;
    fn levelValidate(req: *mut lean_object) -> *mut lean_object;
    fn printEvaluation(req: *mut lean_object) -> *mut lean_object;
    fn checkEvaluate(req: *mut lean_object) -> *mut lean_object;
    fn validateEntities(req: *mut lean_object) -> *mut lean_object;
    fn validateRequest(req: *mut lean_object) -> *mut lean_object;

    fn runCheckAsserts(schema: *mut lean_object, asserts: *mut lean_object) -> *mut lean_object;
    fn printCheckAsserts(schema: *mut lean_object, asserts: *mut lean_object) -> *mut lean_object;
    fn smtLibOfCheckAsserts(
        schema: *mut lean_object,
        asserts: *mut lean_object,
    ) -> *mut lean_object;

    fn assertsOfCheckNeverErrors(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckAlwaysMatches(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckNeverMatches(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckAlwaysAllows(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckAlwaysDenies(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckEquivalent(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckImplies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn assertsOfCheckDisjoint(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn assertsOfCheckMatchesEquivalent(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckMatchesImplies(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckMatchesDisjoint(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;

    fn batchedAuthorizationFFI(req: *mut lean_object) -> *mut lean_object;

    fn isAuthorizedPartial(req: *mut lean_object) -> *mut lean_object;

    fn initialize_Cedar_CedarFFI(builtin: u8, ob: *mut lean_object) -> *mut lean_object;

    fn loadProtobufSchema(req: *mut lean_object) -> *mut lean_object;

    fn generateTypeOfProto(req: *mut lean_object) -> *mut lean_object;
    fn generateSchemaTypeOfProto(req: *mut lean_object) -> *mut lean_object;
    fn illtypedSelfCheck(req: *mut lean_object) -> *mut lean_object;
    fn roundtripPolicySetProto(req: *mut lean_object) -> *mut lean_object;
    fn roundtripSchemaProto(req: *mut lean_object) -> *mut lean_object;

    #[cfg(test)]
    static ffiTestString: *mut lean_object;
    #[cfg(test)]
    static ffiTestExceptOk: *mut lean_object;
    #[cfg(test)]
    static ffiTestExceptErr: *mut lean_object;
}

/// New type wrapper around a `OwnedLeanObject` containing a schema which has already been parsed into a Lean object.
#[derive(Clone, Debug)]
pub struct LeanSchema(OwnedLeanObject);

/// Lean can only be initialized once, use a static variable to know if lean backend needs
/// to be initialized
static START: Once = Once::new();

#[derive(Default)]
/// A struct which will initialize the lean backend (and initialize a thread running the lean runtime)
pub struct CedarLeanFfi {}

/// A macro which converts symcc-request to protobuf, calls the lean code, then deserializes the output
macro_rules! checkPolicy_func {
    // Pattern for function identifier
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:ident, $ret_ty:ty) => {
        checkPolicy_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Pattern for closure expression
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        checkPolicy_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Internal implementation
    (@internal $timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            policy: &Policy,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let response = unsafe { call_lean_ffi_takes_obj_and_protobuf(
                $lean_func_name,
                schema.0,
                &proto::CheckPolicyRequest::new(policy, request_env),
            )};
            match response.as_borrowed().deserialize_into()? {
                ResultDef::Ok(t) => Ok(TimedResult::from_def(t).transform($transform)),
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            }
        }
        pub fn $untimed_func_name(
            &self,
            policy: &Policy,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self
                .$timed_func_name(policy, schema, request_env)?
                .take_result())
        }
    };
}

/// A macro which converts symcc-request to protobuf, calls the lean code, then deserializes the output
macro_rules! checkPolicySet_func {
    // Pattern for function identifier
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:ident, $ret_ty:ty) => {
        checkPolicySet_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Pattern for closure expression
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        checkPolicySet_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Internal implementation
    (@internal $timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            policyset: &PolicySet,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let response = unsafe { call_lean_ffi_takes_obj_and_protobuf(
                $lean_func_name,
                schema.0,
                &proto::CheckPolicySetRequest::new(policyset, request_env),
            )};
            match response.as_borrowed().deserialize_into()? {
                ResultDef::Ok(t) => Ok(TimedResult::from_def(t).transform($transform)),
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            }
        }
        pub fn $untimed_func_name(
            &self,
            policyset: &PolicySet,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self
                .$timed_func_name(policyset, schema, request_env)?
                .take_result())
        }
    };
}

/// A macro which converts symcc-request to protobuf, calls the lean code, then deserializes the output
macro_rules! comparePolicies_func {
    // Pattern for function identifier
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:ident, $ret_ty:ty) => {
        comparePolicies_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Pattern for closure expression
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        comparePolicies_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Internal implementation
    (@internal $timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            src_policy: &Policy,
            tgt_policy: &Policy,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let response = unsafe { call_lean_ffi_takes_obj_and_protobuf(
                $lean_func_name,
                schema.0,
                &proto::ComparePoliciesRequest::new(
                    src_policy,
                    tgt_policy,
                    request_env,
                ),
            )};
            match response.as_borrowed().deserialize_into()? {
                ResultDef::Ok(t) => Ok(TimedResult::from_def(t).transform($transform)),
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            }
        }
        pub fn $untimed_func_name(
            &self,
            src_policy: &Policy,
            tgt_policy: &Policy,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self
                .$timed_func_name(src_policy, tgt_policy, schema, request_env)?
                .take_result())
        }
    };
}

/// A macro which converts symcc-request to protobuf, calls the lean code, then deserializes the output
macro_rules! comparePolicySet_func {
    // Pattern for function identifier
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:ident, $ret_ty:ty) => {
        comparePolicySet_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Pattern for closure expression
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        comparePolicySet_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Internal implementation
    (@internal $timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            src_policyset: &PolicySet,
            tgt_policyset: &PolicySet,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let response = unsafe { call_lean_ffi_takes_obj_and_protobuf(
                $lean_func_name,
                schema.0,
                &proto::ComparePolicySetsRequest::new(
                    src_policyset,
                    tgt_policyset,
                    request_env,
                ),
            )};
            match response.as_borrowed().deserialize_into()? {
                ResultDef::Ok(t) => Ok(TimedResult::from_def(t).transform($transform)),
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            }
        }
        pub fn $untimed_func_name(
            &self,
            src_policyset: &PolicySet,
            tgt_policyset: &PolicySet,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self
                .$timed_func_name(src_policyset, tgt_policyset, schema, request_env)?
                .take_result())
        }
    };
}

/// A macro which converts symcc-request to protobuf, calls the lean code, then deserializes the output
///
/// We could easily create the `*GivenRawModel` variants of the other macros, but today we only need this one
macro_rules! comparePolicySetGivenRawModel_func {
    // Pattern for function identifier
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:ident, $ret_ty:ty) => {
        comparePolicySetGivenRawModel_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Pattern for closure expression
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        comparePolicySetGivenRawModel_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Internal implementation
    (@internal $timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            src_policyset: &PolicySet,
            tgt_policyset: &PolicySet,
            schema: LeanSchema,
            request_env: &RequestEnv,
            raw_model: &str,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let response = unsafe { call_lean_ffi_takes_obj_protobuf_and_string(
                $lean_func_name,
                schema.0,
                &proto::ComparePolicySetsRequest::new(
                    src_policyset,
                    tgt_policyset,
                    request_env,
                ),
                raw_model,
            )};
            match response.as_borrowed().deserialize_into()? {
                ResultDef::Ok(t) => Ok(TimedResult::from_def(t).transform($transform)),
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            }
        }
        pub fn $untimed_func_name(
            &self,
            src_policyset: &PolicySet,
            tgt_policyset: &PolicySet,
            schema: LeanSchema,
            request_env: &RequestEnv,
            raw_model: &str,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self
                .$timed_func_name(src_policyset, tgt_policyset, schema, request_env, raw_model)?
                .take_result())
        }
    };
}

macro_rules! checkAsserts_func {
    // Pattern for function identifier
    (&timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:ident, $ret_ty:ty) => {
        checkAsserts_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Pattern for closure expression
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        checkAsserts_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Internal implementation
    (@internal $timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            asserts: &[Term],
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let response = unsafe { call_lean_ffi_takes_obj_and_protobuf(
                $lean_func_name,
                schema.0,
                &proto::CheckAssertsRequest::new(asserts, request_env),
            )};
            match response.as_borrowed().deserialize_into()? {
                ResultDef::Ok(t) => Ok(TimedResult::from_def(t).transform($transform)),
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            }
        }
        pub fn $untimed_func_name(
            &self,
            asserts: &[Term],
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self.$timed_func_name(asserts, schema, request_env)?.take_result())
        }
    };
}

impl CedarLeanFfi {
    /// WARNING: we can only have one Lean thread
    pub fn new() -> Self {
        START.call_once(|| {
            unsafe {
                // following: https://lean-lang.org/lean4/doc/dev/ffi.html
                lean_initialize_runtime_module_locked();
                let builtin: u8 = 1;
                let res = initialize_Cedar_CedarFFI(builtin, lean_io_mk_world());
                if lean_io_result_is_ok(res) {
                    lean_dec_ref(res);
                } else {
                    lean_io_result_show_error(res);
                    lean_dec(res);
                    panic!("Failed to initialize Lean");
                }
                lean_io_mark_end_initialization();
                // If we don't explicitly set this, Lean does not abort after hitting a panic
                lean_set_exit_on_panic(true);
            };
        });
        unsafe { lean_initialize_thread() };
        Self {}
    }

    // Adds each of the run_(symcc-command) to call the corresponding lean function
    // returns true if the check definitely holds and false if it definitely doesn't
    // returns an error if the lean could not successfully run the solver or if the solver returned unknown
    checkPolicy_func!(
        run_check_never_errors_timed,
        run_check_never_errors,
        runCheckNeverErrors,
        |x| x,
        bool
    );

    checkPolicy_func!(
        run_check_never_errors_with_cex_timed,
        run_check_never_errors_with_cex,
        runCheckNeverErrorsWithCex,
        |x| x,
        Option<Env>
    );

    checkPolicy_func!(
        run_check_always_matches_timed,
        run_check_always_matches,
        runCheckAlwaysMatches,
        |x| x,
        bool
    );

    checkPolicy_func!(
        run_check_always_matches_with_cex_timed,
        run_check_always_matches_with_cex,
        runCheckAlwaysMatchesWithCex,
        |x| x,
        Option<Env>
    );

    checkPolicy_func!(
        run_check_never_matches_timed,
        run_check_never_matches,
        runCheckNeverMatches,
        |x| x,
        bool
    );

    checkPolicy_func!(
        run_check_never_matches_with_cex_timed,
        run_check_never_matches_with_cex,
        runCheckNeverMatchesWithCex,
        |x| x,
        Option<Env>
    );

    checkPolicySet_func!(
        run_check_always_allows_timed,
        run_check_always_allows,
        runCheckAlwaysAllows,
        |x| x,
        bool
    );

    checkPolicySet_func!(
        run_check_always_allows_with_cex_timed,
        run_check_always_allows_with_cex,
        runCheckAlwaysAllowsWithCex,
        |x| x,
        Option<Env>
    );

    checkPolicySet_func!(
        run_check_always_denies_timed,
        run_check_always_denies,
        runCheckAlwaysDenies,
        |x| x,
        bool
    );

    checkPolicySet_func!(
        run_check_always_denies_with_cex_timed,
        run_check_always_denies_with_cex,
        runCheckAlwaysDeniesWithCex,
        |x| x,
        Option<Env>
    );

    comparePolicySet_func!(
        run_check_equivalent_timed,
        run_check_equivalent,
        runCheckEquivalent,
        |x| x,
        bool
    );

    comparePolicySet_func!(
        run_check_equivalent_with_cex_timed,
        run_check_equivalent_with_cex,
        runCheckEquivalentWithCex,
        |x| x,
        Option<Env>
    );

    comparePolicySetGivenRawModel_func!(
        run_check_equivalent_with_cex_given_raw_model_timed,
        run_check_equivalent_with_cex_given_raw_model,
        runCheckEquivalentWithCexGivenRawModel,
        |x| x,
        Env
    );

    comparePolicySet_func!(
        run_check_implies_timed,
        run_check_implies,
        runCheckImplies,
        |x| x,
        bool
    );

    comparePolicySet_func!(
        run_check_implies_with_cex_timed,
        run_check_implies_with_cex,
        runCheckImpliesWithCex,
        |x| x,
        Option<Env>
    );

    comparePolicySetGivenRawModel_func!(
        run_check_implies_with_cex_given_raw_model_timed,
        run_check_implies_with_cex_given_raw_model,
        runCheckImpliesWithCexGivenRawModel,
        |x| x,
        Env
    );

    comparePolicySet_func!(
        run_check_disjoint_timed,
        run_check_disjoint,
        runCheckDisjoint,
        |x| x,
        bool
    );

    comparePolicySet_func!(
        run_check_disjoint_with_cex_timed,
        run_check_disjoint_with_cex,
        runCheckDisjointWithCex,
        |x| x,
        Option<Env>
    );

    comparePolicySetGivenRawModel_func!(
        run_check_disjoint_with_cex_given_raw_model_timed,
        run_check_disjoint_with_cex_given_raw_model,
        runCheckDisjointWithCexGivenRawModel,
        |x| x,
        Env
    );

    comparePolicies_func!(
        run_check_matches_equivalent_timed,
        run_check_matches_equivalent,
        runCheckMatchesEquivalent,
        |x| x,
        bool
    );

    comparePolicies_func!(
        run_check_matches_equivalent_with_cex_timed,
        run_check_matches_equivalent_with_cex,
        runCheckMatchesEquivalentWithCex,
        |x| x,
        Option<Env>
    );

    comparePolicies_func!(
        run_check_matches_implies_timed,
        run_check_matches_implies,
        runCheckMatchesImplies,
        |x| x,
        bool
    );

    comparePolicies_func!(
        run_check_matches_implies_with_cex_timed,
        run_check_matches_implies_with_cex,
        runCheckMatchesImpliesWithCex,
        |x| x,
        Option<Env>
    );

    comparePolicies_func!(
        run_check_matches_disjoint_timed,
        run_check_matches_disjoint,
        runCheckMatchesDisjoint,
        |x| x,
        bool
    );

    comparePolicies_func!(
        run_check_matches_disjoint_with_cex_timed,
        run_check_matches_disjoint_with_cex,
        runCheckMatchesDisjointWithCex,
        |x| x,
        Option<Env>
    );

    // Adds each of the print_(symcc-command) to call the corresponding lean function
    checkPolicy_func!(
        print_check_never_errors_timed,
        print_check_never_errors,
        printCheckNeverErrors,
        |x| x,
        ()
    );

    checkPolicySet_func!(
        print_check_always_allows_timed,
        print_check_always_allows,
        printCheckAlwaysAllows,
        |x| x,
        ()
    );

    checkPolicySet_func!(
        print_check_always_denies_timed,
        print_check_always_denies,
        printCheckAlwaysDenies,
        |x| x,
        ()
    );

    comparePolicySet_func!(
        print_check_equivalent_timed,
        print_check_equivalent,
        printCheckEquivalent,
        |x| x,
        ()
    );

    comparePolicySet_func!(
        print_check_implies_timed,
        print_check_implies,
        printCheckImplies,
        |x| x,
        ()
    );

    comparePolicySet_func!(
        print_check_disjoint_timed,
        print_check_disjoint,
        printCheckDisjoint,
        |x| x,
        ()
    );

    checkAsserts_func!(
        run_check_asserts_timed,
        run_check_asserts,
        runCheckAsserts,
        |x| x,
        bool
    );

    checkAsserts_func!(
        print_check_asserts_timed,
        print_check_asserts,
        printCheckAsserts,
        |x| x,
        ()
    );

    checkAsserts_func!(
        smtlib_of_check_asserts_timed,
        smtlib_of_check_asserts,
        smtLibOfCheckAsserts,
        |x| x,
        String
    );

    checkPolicy_func!(
        asserts_of_check_never_errors_timed,
        asserts_of_check_never_errors,
        assertsOfCheckNeverErrors,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    checkPolicy_func!(
        asserts_of_check_always_matches_timed,
        asserts_of_check_always_matches,
        assertsOfCheckAlwaysMatches,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    checkPolicy_func!(
        asserts_of_check_never_matches_timed,
        asserts_of_check_never_matches,
        assertsOfCheckNeverMatches,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    checkPolicySet_func!(
        asserts_of_check_always_allows_timed,
        asserts_of_check_always_allows,
        assertsOfCheckAlwaysAllows,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    checkPolicySet_func!(
        asserts_of_check_always_denies_timed,
        asserts_of_check_always_denies,
        assertsOfCheckAlwaysDenies,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicySet_func!(
        asserts_of_check_equivalent_timed,
        asserts_of_check_equivalent,
        assertsOfCheckEquivalent,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicySet_func!(
        asserts_of_check_implies_timed,
        asserts_of_check_implies,
        assertsOfCheckImplies,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicySet_func!(
        asserts_of_check_disjoint_timed,
        asserts_of_check_disjoint,
        assertsOfCheckDisjoint,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicies_func!(
        asserts_of_check_matches_equivalent_timed,
        asserts_of_check_matches_equivalent,
        assertsOfCheckMatchesEquivalent,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicies_func!(
        asserts_of_check_matches_implies_timed,
        asserts_of_check_matches_implies,
        assertsOfCheckMatchesImplies,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicies_func!(
        asserts_of_check_matches_disjoint_timed,
        asserts_of_check_matches_disjoint,
        assertsOfCheckMatchesDisjoint,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    // Adds each of the smtlib_of_(symcc-command) to call the corresponding lean function
    checkPolicy_func!(
        smtlib_of_check_never_errors_timed,
        smtlib_of_check_never_errors,
        smtLibOfCheckNeverErrors,
        |x| x,
        String
    );

    checkPolicySet_func!(
        smtlib_of_check_always_allows_timed,
        smtlib_of_check_always_allows,
        smtLibOfCheckAlwaysAllows,
        |x| x,
        String
    );

    checkPolicySet_func!(
        smtlib_of_check_always_denies_timed,
        smtlib_of_check_always_denies,
        smtLibOfCheckAlwaysDenies,
        |x| x,
        String
    );

    comparePolicySet_func!(
        smtlib_of_check_equivalent_timed,
        smtlib_of_check_equivalent,
        smtLibOfCheckEquivalent,
        |x| x,
        String
    );

    comparePolicySet_func!(
        smtlib_of_check_implies_timed,
        smtlib_of_check_implies,
        smtLibOfCheckImplies,
        |x| x,
        String
    );

    comparePolicySet_func!(
        smtlib_of_check_disjoint_timed,
        smtlib_of_check_disjoint,
        smtLibOfCheckDisjoint,
        |x| x,
        String
    );

    /// Calls the lean backend to determine if the `Request` is allowed
    /// by the `PolicySet` given the provided set of `Entities`
    pub fn is_authorized_timed(
        &self,
        policyset: &PolicySet,
        entities: &Entities,
        request: &Request,
    ) -> Result<TimedResult<AuthorizationResponse>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                isAuthorized,
                &proto::AuthorizationRequest::new(policyset, entities, request),
            )
        };
        match response
            .as_borrowed()
            .deserialize_into::<ResultDef<TimedDef<AuthorizationResponseInner>>>()?
        {
            ResultDef::Ok(resp) => {
                let tdef = TimedDef {
                    data: AuthorizationResponse::from_inner(resp.data)?,
                    duration: resp.duration,
                };
                Ok(TimedResult::from_def(tdef))
            }
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn is_authorized(
        &self,
        policyset: &PolicySet,
        entities: &Entities,
        request: &Request,
    ) -> Result<AuthorizationResponse, FfiError> {
        Ok(self
            .is_authorized_timed(policyset, entities, request)?
            .take_result())
    }

    /// Calls the lean backend to print the evaluation of the input Cedar `Expression`
    pub fn print_evaluation_timed(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
    ) -> Result<TimedResult<()>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                printEvaluation,
                &proto::EvaluationRequestChecked::new(input_expr, entities, request),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(t) => Ok(TimedResult::from_def(t)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn print_evaluation(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
    ) -> Result<(), FfiError> {
        self.print_evaluation_timed(input_expr, entities, request)?;
        Ok(())
    }

    /// Calls the lean backend and returns `true` if the input Cedar `Expression`
    /// evaluates to the output cedar `Expression`
    pub fn check_evaluate_timed(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
        output_expr: Option<&Expression>,
    ) -> Result<TimedResult<bool>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                checkEvaluate,
                &proto::EvaluationRequestChecked::new_checked(
                    input_expr,
                    entities,
                    request,
                    output_expr,
                ),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(are_eq) => Ok(TimedResult::from_def(are_eq)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn check_evaluate(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
        output_expr: Option<&Expression>,
    ) -> Result<bool, FfiError> {
        Ok(self
            .check_evaluate_timed(input_expr, entities, request, output_expr)?
            .take_result())
    }

    /// Calls the lean backend to validate the `PolicySet` against the provided `Schema`
    pub fn validate_timed(
        &self,
        policyset: &PolicySet,
        schema: &Schema,
        mode: &ValidationMode,
    ) -> Result<TimedResult<ValidationResponse>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                validate,
                &proto::ValidationRequest::new(policyset, schema, mode),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(res) => Ok(TimedResult::from_def(res)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn validate(
        &self,
        policyset: &PolicySet,
        schema: &Schema,
        mode: &ValidationMode,
    ) -> Result<ValidationResponse, FfiError> {
        Ok(self.validate_timed(policyset, schema, mode)?.take_result())
    }

    /// Calls the lean backend to validate the `PolicySet` against the provided `Schema` at level `level`
    pub fn level_validate_timed(
        &self,
        policyset: &PolicySet,
        schema: &Schema,
        level: i32,
    ) -> Result<TimedResult<ValidationResponse>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                levelValidate,
                &proto::LevelValidationRequest::new(policyset, schema, level),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(res) => Ok(TimedResult::from_def(res)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn level_validate(
        &self,
        policyset: &PolicySet,
        schema: &Schema,
        level: i32,
    ) -> Result<ValidationResponse, FfiError> {
        Ok(self
            .level_validate_timed(policyset, schema, level)?
            .take_result())
    }

    /// Calls the lean backend to validate the `Entities` against the provided `Schema`
    pub fn validate_entities_timed(
        &self,
        schema: &Schema,
        entities: &Entities,
    ) -> Result<TimedResult<ValidationResponse>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                validateEntities,
                &proto::EntityValidationRequest::new(schema, entities),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(res) => Ok(TimedResult::from_def(res)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn validate_entities(
        &self,
        schema: &Schema,
        entities: &Entities,
    ) -> Result<ValidationResponse, FfiError> {
        Ok(self
            .validate_entities_timed(schema, entities)?
            .take_result())
    }

    /// Calls the lean backend to validate the `Request` against the provided `Schema`
    pub fn validate_request_timed(
        &self,
        schema: &Schema,
        request: &Request,
    ) -> Result<TimedResult<ValidationResponse>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                validateRequest,
                &proto::RequestValidationRequest::new(schema, request),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(res) => Ok(TimedResult::from_def(res)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn validate_request(
        &self,
        schema: &Schema,
        request: &Request,
    ) -> Result<ValidationResponse, FfiError> {
        Ok(self.validate_request_timed(schema, request)?.take_result())
    }

    /// Calls the lean backend to perform batched authorization
    pub fn batched_authorization_timed(
        &self,
        policyset: &PolicySet,
        schema: &Schema,
        request: &Request,
        entities: &Entities,
        iteration: u32,
    ) -> Result<TimedResult<TpeResponse>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                batchedAuthorizationFFI,
                &proto::BatchedAuthorizationRequest::new(
                    &policyset, schema, request, entities, iteration,
                ),
            )
        };
        response
            .as_borrowed()
            .deserialize_into::<ResultDef<TimedDef<ResultDef<TpeResponseInner>>>>()?
            .to_result()
            .map_err(FfiError::LeanBackendError)?
            .to_timed_result()
            .transform_m(ResultDef::to_result)
            .map_err(FfiError::LeanBackendError)?
            .transform_m(TpeResponse::from_inner)
    }

    pub fn batched_authorization(
        &self,
        policy: &PolicySet,
        schema: &Schema,
        request: &Request,
        entities: &Entities,
        iteration: u32,
    ) -> Result<TpeResponse, FfiError> {
        Ok(self
            .batched_authorization_timed(policy, schema, request, entities, iteration)?
            .take_result())
    }

    pub fn load_lean_schema_object(&self, schema: &Schema) -> Result<LeanSchema, FfiError> {
        let lean_schema_object = unsafe {
            call_lean_ffi_takes_protobuf(
                loadProtobufSchema,
                &cedar_policy::proto::models::Schema::from(schema),
            )
        };
        match lean_schema_object.as_borrowed().as_result()? {
            Ok(lean_ok_obj) => Ok(LeanSchema(lean_ok_obj.to_owned())),
            Err(lean_err_obj) => Err(FfiError::LeanBackendError(
                lean_err_obj.as_rust_str()?.to_string(),
            )),
        }
    }

    /// Generate well-typed expressions and return protobuf-encoded PolicySet bytes.
    pub fn generate_typeof_proto(&self, params: &serde_json::Value) -> Result<Vec<u8>, FfiError> {
        let request_bytes = params.to_string().into_bytes();
        let arg = OwnedLeanObject::new_array_from_buf(&request_bytes);
        let response = unsafe { call_lean_ffi_function(generateTypeOfProto, arg) };
        let bytes = response.as_borrowed().as_byte_array()?;
        Ok(bytes.to_vec())
    }

    /// Generate a random well-formed schema + well-typed expression and return protobuf bytes.
    pub fn generate_schema_typeof_proto(
        &self,
        params: &serde_json::Value,
    ) -> Result<Vec<u8>, FfiError> {
        let request_bytes = params.to_string().into_bytes();
        let arg = OwnedLeanObject::new_array_from_buf(&request_bytes);
        let response = unsafe { call_lean_ffi_function(generateSchemaTypeOfProto, arg) };
        let bytes = response.as_borrowed().as_byte_array()?;
        Ok(bytes.to_vec())
    }

    /// Run the ill-typed generator self-check COMPILED: generate the error corpus and
    /// validate each policy with the Lean `validate` before any proto encoding. Returns a
    /// JSON UTF-8 byte string `{envs, generated, rejected, accepted, samples:[repr,...]}`.
    /// `accepted > 0` means the generator emitted a well-typed policy (unsound).
    pub fn illtyped_self_check(&self, params: &serde_json::Value) -> Result<Vec<u8>, FfiError> {
        let request_bytes = params.to_string().into_bytes();
        let arg = OwnedLeanObject::new_array_from_buf(&request_bytes);
        let response = unsafe { call_lean_ffi_function(illtypedSelfCheck, arg) };
        let bytes = response.as_borrowed().as_byte_array()?;
        Ok(bytes.to_vec())
    }

    /// Decode a protobuf-encoded `PolicySet`, link its templates into concrete
    /// policies in the Lean spec, and re-encode them with the Lean encoder.
    ///
    /// This drives both the Lean decoder (`CedarProto`) and the Lean encoder
    /// (`CedarProto.Encode.encodePolicies`) so a caller can check cross-language
    /// proto fidelity: `Rust encode -> here -> Rust decode` should preserve the
    /// policy set. Returns empty bytes if the Lean decode fails.
    pub fn roundtrip_policyset_proto(&self, proto_bytes: &[u8]) -> Result<Vec<u8>, FfiError> {
        let arg = OwnedLeanObject::new_array_from_buf(proto_bytes);
        let response = unsafe { call_lean_ffi_function(roundtripPolicySetProto, arg) };
        let bytes = response.as_borrowed().as_byte_array()?;
        Ok(bytes.to_vec())
    }

    /// Decode a protobuf-encoded `Schema`, link it into a `Cedar.Validation.Schema`
    /// in the Lean spec, and re-encode it with the Lean encoder (`encodeSchema`).
    ///
    /// Companion to [`Self::roundtrip_policyset_proto`] for schemas: it drives the
    /// Lean schema decoder and encoder, including the ancestor⇄descendant inversion,
    /// so a caller can check `Rust encode -> here -> Rust decode` preserves the
    /// schema. Returns empty bytes if the Lean decode fails.
    pub fn roundtrip_schema_proto(&self, proto_bytes: &[u8]) -> Result<Vec<u8>, FfiError> {
        let arg = OwnedLeanObject::new_array_from_buf(proto_bytes);
        let response = unsafe { call_lean_ffi_function(roundtripSchemaProto, arg) };
        let bytes = response.as_borrowed().as_byte_array()?;
        Ok(bytes.to_vec())
    }
}

/// uninitialize lean thread when done
impl Drop for CedarLeanFfi {
    fn drop(&mut self) {
        unsafe { lean_finalize_thread() }
    }
}

#[cfg(test)]
mod test {
    /***************** Copy Extern Block so that Tests are also linked with lean code *****************/
    #[allow(clippy::duplicated_attributes)]
    #[link(name = "Cedar_Cedar", kind = "static")]
    #[link(name = "Cedar_Cedar_SymCC", kind = "static")]
    #[link(name = "Cedar_Protobuf", kind = "static")]
    #[link(name = "Cedar_CedarProto", kind = "static")]
    #[link(name = "batteries_Batteries", kind = "static")]
    #[link(name = "Cedar_CedarFFI", kind = "static")]
    unsafe extern "C" {}

    use cedar_policy::{
        Context, Entities, Entity, EntityTypeName, EntityUid, Expression, Policy, PolicyId,
        PolicySet, Request, RequestEnv, Schema, ValidationMode,
    };
    use cool_asserts::assert_matches;

    use std::collections::HashSet;
    use std::marker::PhantomData;
    use std::str::FromStr;

    use crate::{
        CedarLeanFfi, TimedResult, ValidationResponse,
        lean_ffi::{ffiTestExceptErr, ffiTestExceptOk, ffiTestString},
        lean_object::LeanObject,
    };

    impl CedarLeanFfi {
        fn ffi_test_string(&self) -> LeanObject<'static> {
            unsafe { LeanObject(ffiTestString, PhantomData) }
        }

        fn ffi_test_except_ok(&self) -> LeanObject<'static> {
            unsafe { LeanObject(ffiTestExceptOk, PhantomData) }
        }

        fn ffi_test_except_err(&self) -> LeanObject<'static> {
            unsafe { LeanObject(ffiTestExceptErr, PhantomData) }
        }
    }

    #[test]
    fn read_test_string() {
        let ffi = CedarLeanFfi::new();
        let rust_str = ffi.ffi_test_string().as_rust_str().unwrap();
        assert_eq!(rust_str, "ffiTestString");
    }

    #[test]
    fn read_test_except_ok() {
        let ffi = CedarLeanFfi::new();
        let ok_str = ffi
            .ffi_test_except_ok()
            .as_ctor()
            .unwrap()
            .as_result()
            .unwrap()
            .unwrap()
            .as_rust_str()
            .unwrap();
        assert_eq!(ok_str, "ok");
    }

    #[test]
    fn read_test_except_err() {
        let ffi = CedarLeanFfi::new();
        let err_str = ffi
            .ffi_test_except_err()
            .as_ctor()
            .unwrap()
            .as_result()
            .unwrap()
            .unwrap_err()
            .as_rust_str()
            .unwrap();
        assert_eq!(err_str, "error");
    }

    fn example_schema() -> Schema {
        Schema::from_cedarschema_str(
            r#"
            entity Account;
            entity Identity {
                account: Account
            };
            entity Thing in Account {
                owner: Identity,
                description: String,
                private: Bool
            };
            action view appliesTo {
            principal: [Identity],
            resource: [Thing],
            context: {
                n1: String
            }
            };
            "#,
        )
        .expect("Example schema failed to parse")
        .0
    }

    #[test]
    fn load_schema() {
        let ffi = CedarLeanFfi::new();
        let schema = example_schema();
        let t = ffi.load_lean_schema_object(&schema);
        t.unwrap();
    }

    fn request(principal: &str, action: &str, resource: &str) -> Request {
        let principal = EntityUid::from_str(principal).expect("Failed to parse principal");
        let action = EntityUid::from_str(action).expect("Failed to parse action");
        let resource = EntityUid::from_str(resource).expect("Failed to parse resource");
        let ctx = Context::from_pairs([(
            "n1".to_string(),
            cedar_policy::RestrictedExpression::new_string("Some value".to_string()),
        )])
        .expect("Failed to construct context");
        Request::new(principal, action, resource, ctx, None).expect("Failed to construct request")
    }

    fn request_env(principal_type: &str, action: &str, resource_type: &str) -> RequestEnv {
        let principal_type =
            EntityTypeName::from_str(principal_type).expect("Failed to parse principal type");
        let action = EntityUid::from_str(action).expect("Failed to parse action");
        let resource_type =
            EntityTypeName::from_str(resource_type).expect("Failed to parse resource type");
        RequestEnv::new(principal_type, action, resource_type)
    }

    #[test]
    fn test_check_never_errors() {
        let trivial_policy = Policy::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_never_errors(&trivial_policy, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for run_check_never_errors");
        assert!(
            res,
            "run_check_never_errors returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_never_errors(&trivial_policy, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for smtlib_of_check_never_errors");

        ffi.asserts_of_check_never_errors(&trivial_policy, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_never_errors")
            .expect(
                "Lean SymCC unexpectedly failed to encode term for asserts_of_check_never_errors",
            );
    }

    #[test]
    fn test_check_always_allows() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_always_allows(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for run_check_always_allows");
        assert!(
            res,
            "run_check_always_allows returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_always_allows(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for smtlib_of_check_always_allows");

        ffi.asserts_of_check_always_allows(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_always_allows")
            .expect(
                "Lean SymCC unexpectedly failed to encode term for asserts_of_check_always_allows",
            );

        let res = ffi
            .run_check_always_allows(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for run_check_always_allows");
        assert!(
            !res,
            "run_check_always_allows returned wrong result. Expected: false"
        );

        ffi.smtlib_of_check_always_allows(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for smtlib_of_check_always_allows");

        ffi.asserts_of_check_always_allows(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_always_allows")
            .expect(
                "Lean SymCC unexpectedly failed to encode term for asserts_of_check_always_allows",
            );
    }

    #[test]
    fn test_check_always_denies() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_always_denies(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for run_check_always_denies");
        assert!(
            !res,
            "run_check_always_denies returned wrong result. Expected: false"
        );

        ffi.smtlib_of_check_always_denies(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for smtlib_of_check_always_denies");

        ffi.asserts_of_check_always_denies(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_always_denies")
            .expect(
                "Lean SymCC unexpectedly failed to encode term for asserts_of_check_always_denies",
            );

        let res = ffi
            .run_check_always_denies(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for run_check_always_denies");
        assert!(
            res,
            "run_check_always_denies returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_always_denies(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for smtlib_of_check_always_denies");

        ffi.asserts_of_check_always_denies(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_always_denies")
            .expect(
                "Lean SymCC unexpectedly failed to encode term for asserts_of_check_always_denies",
            );
    }

    #[test]
    fn test_check_equivalent() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_equivalent(
                &always_allows_pset,
                &always_allows_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_equivalent");
        assert!(
            res,
            "run_check_equivalent returned wrong result. Expected: true"
        );

        ffi.asserts_of_check_equivalent(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_equivalent")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_equivalent");

        ffi.smtlib_of_check_equivalent(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_equivalent");

        let res = ffi
            .run_check_equivalent(
                &always_denies_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_equivalent");
        assert!(
            res,
            "run_check_equivalent returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_equivalent(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_equivalent");

        ffi.asserts_of_check_equivalent(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_equivalent")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_equivalent");

        let res = ffi
            .run_check_equivalent(
                &always_allows_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_equivalent");
        assert!(
            !res,
            "run_check_equivalent returned wrong result. Expected: false"
        );

        ffi.smtlib_of_check_equivalent(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_equivalent");

        ffi.asserts_of_check_equivalent(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_equivalent")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_equivalent");
    }

    #[test]
    fn test_check_implies() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_implies(
                &always_allows_pset,
                &always_allows_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_implies");
        assert!(
            res,
            "run_check_implies returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_implies(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_implies");

        ffi.asserts_of_check_implies(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_implies")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_implies");

        let res = ffi
            .run_check_implies(
                &always_denies_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_implies");
        assert!(
            res,
            "run_check_implies returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_implies(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_implies");

        ffi.asserts_of_check_implies(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_implies")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_implies");

        let res = ffi
            .run_check_implies(
                &always_allows_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_implies");
        assert!(
            !res,
            "run_check_implies returned wrong result. Expected: false"
        );

        ffi.smtlib_of_check_implies(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_implies");

        ffi.asserts_of_check_implies(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_implies")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_implies");

        let res = ffi
            .run_check_implies(
                &always_denies_pset,
                &always_allows_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_implies");
        assert!(
            res,
            "run_check_implies returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_implies(
            &always_denies_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_implies");

        ffi.asserts_of_check_implies(&always_denies_pset, &always_allows_pset, schema, &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_implies")
            .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_implies");
    }

    #[test]
    fn test_check_disjoint() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_disjoint(
                &always_allows_pset,
                &always_allows_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_disjoint");
        assert!(
            !res,
            "run_check_disjoint returned wrong result. Expected: false"
        );

        ffi.smtlib_of_check_disjoint(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_disjoint");

        ffi.asserts_of_check_disjoint(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_disjoint")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_disjoint");

        let res = ffi
            .run_check_disjoint(
                &always_denies_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_disjoint");
        assert!(
            res,
            "run_check_disjoint returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_disjoint(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_disjoint");

        ffi.asserts_of_check_disjoint(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_disjoint")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_disjoint");

        let res = ffi
            .run_check_disjoint(
                &always_allows_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_disjoint");
        assert!(
            res,
            "run_check_disjoint returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_disjoint(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_disjoint");

        ffi.asserts_of_check_disjoint(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_disjoint")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_disjoint");

        let res = ffi
            .run_check_disjoint(
                &always_denies_pset,
                &always_allows_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_disjoint");
        assert!(
            res,
            "run_check_disjoint returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_disjoint(
            &always_denies_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_disjoint");

        ffi.asserts_of_check_disjoint(
            &always_denies_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_disjoint")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_disjoint");
    }

    #[test]
    fn test_is_authorized() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let req = request(
            "Identity::\"Alice\"",
            "Action::\"view\"",
            "Thing::\"Thing1\"",
        );
        let principal = Entity::with_uid(req.principal().unwrap().clone());
        let action = Entity::with_uid(req.action().unwrap().clone());
        let resource = Entity::with_uid(req.resource().unwrap().clone());
        let entities = Entities::from_entities(vec![principal, action, resource], None)
            .expect("Failed to construct entities");

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .is_authorized(&always_allows_pset, &entities, &req)
            .expect("Lean call unexpectedly failed for is_authorized");

        assert_eq!(res.decision(), cedar_policy::Decision::Allow);
        let deciding_policies = HashSet::from_iter(vec![PolicyId::from_str("policy0").unwrap()]);
        assert_eq!(*res.determining_policies(), deciding_policies);
        assert!(
            res.erroring_policies().is_empty(),
            "Always allows policyset should have no erroring policies"
        );

        let res = ffi
            .is_authorized(&always_denies_pset, &entities, &req)
            .expect("Lean call unexpectedly failed for is_authorized");
        assert_eq!(res.decision(), cedar_policy::Decision::Deny);
        assert_eq!(*res.determining_policies(), deciding_policies);
        assert!(
            res.erroring_policies().is_empty(),
            "Always denies policyset should have no erroring policies"
        );
    }

    #[test]
    fn test_print_evaluate() {
        let input_expr = Expression::from_str("1 + 2").expect("Failed to parse expression");
        let err_expr = Expression::from_str("1 + true").expect("Failed to parse expression");
        let entities = Entities::empty();
        let req = request(
            "Identity::\"Alice\"",
            "Action::\"view\"",
            "Thing::\"Thing1\"",
        );

        let ffi = CedarLeanFfi::new();

        ffi.print_evaluation(&input_expr, &entities, &req)
            .expect("Lean call unexpectedly failed for check_evaluate");

        // Erroring expressions should print the evaluation error, not result in an FFI error.
        ffi.print_evaluation(&err_expr, &entities, &req)
            .expect("Lean call unexpectedly failed for check_evaluate");
    }

    #[test]
    fn test_check_evaluate() {
        let input_expr = Expression::from_str("1 + 2").expect("Failed to parse expression");
        let eval_expr = Expression::from_str("3").expect("Failed to parse expression");
        let wrong_expr = Expression::from_str("2").expect("Failed to parse expression");
        let entities = Entities::empty();
        let req = request(
            "Identity::\"Alice\"",
            "Action::\"view\"",
            "Thing::\"Thing1\"",
        );

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .check_evaluate(&input_expr, &entities, &req, Some(&eval_expr))
            .expect("Lean call unexpectedly failed for check_evaluate");
        assert!(res, "check_evaluate returned wrong result: Expected true");

        let res = ffi
            .check_evaluate(&input_expr, &entities, &req, Some(&wrong_expr))
            .expect("Lean call unexpectedly failed for check_evaluate");
        assert!(!res, "check_evaluate returned wrong result: Expected false");
    }

    #[test]
    fn test_validate() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let schema = example_schema();
        let mode = ValidationMode::Strict;

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .validate(&always_allows_pset, &schema, &mode)
            .expect("Lean call unexpectedly failed for validate");
        assert_eq!(res, ValidationResponse::Ok(()));
    }

    #[test]
    fn test_level_validate() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let schema = example_schema();

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .level_validate(&always_allows_pset, &schema, 0)
            .expect("Lean call unexpectedly failed for level_validate");
        assert_eq!(res, ValidationResponse::Ok(()));
    }

    #[test]
    fn test_validate_entities() {
        let schema = example_schema();
        let account = Entity::with_uid(EntityUid::from_str("Account::\"account\"").unwrap());
        let action = Entity::with_uid(EntityUid::from_str("Action::\"view\"").unwrap());
        let entities = Entities::from_entities(vec![account, action], None)
            .expect("Failed to construct entities");

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .validate_entities(&schema, &entities)
            .expect("Lean call unexpectedly failed for validate_entities");
        assert_eq!(res, ValidationResponse::Ok(()));
    }

    #[test]
    fn test_validate_request() {
        let schema = example_schema();
        let req = request(
            "Identity::\"Alice\"",
            "Action::\"view\"",
            "Thing::\"thing1\"",
        );

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .validate_request(&schema, &req)
            .expect("Lean call unexpectedly failed for validate_request");
        assert_eq!(res, ValidationResponse::Ok(()));
    }

    #[test]
    fn test_cex() {
        let ffi = CedarLeanFfi::new();
        let schema = ffi
            .load_lean_schema_object(
                &Schema::from_str(
                    r#"
        entity a {
          r : Bool,
        };
        action "action" appliesTo {
          principal: a,
          resource: a,
        };
        "#,
                )
                .unwrap(),
            )
            .unwrap();
        let ps = PolicySet::from_str(
            r#"
        permit(
      principal,
      action in [Action::"action"],
      resource
    ) when {
      ((true && (a::"*"["r"])) && true) && true
    };"#,
        )
        .unwrap();
        let req_env = request_env("a", "Action::\"action\"", "a");

        assert_matches!(
            ffi.run_check_always_denies_with_cex_timed(&ps, schema.clone(), &req_env),
            Ok(TimedResult {
                result: Some(_),
                ..
            })
        );
        assert_matches!(
            ffi.run_check_always_denies_timed(&ps, schema.clone(), &req_env),
            Ok(TimedResult { result: false, .. })
        );

        assert_matches!(
            ffi.run_check_always_allows_with_cex_timed(&ps, schema.clone(), &req_env),
            Ok(TimedResult {
                result: Some(_),
                ..
            })
        );
        assert_matches!(
            ffi.run_check_always_allows_timed(&ps, schema.clone(), &req_env),
            Ok(TimedResult { result: false, .. })
        );

        assert_matches!(
            ffi.run_check_never_errors_with_cex_timed(
                ps.policies().next().unwrap(),
                schema.clone(),
                &req_env,
            ),
            Ok(TimedResult { result: None, .. })
        );
        assert_matches!(
            ffi.run_check_never_errors_timed(
                ps.policies().next().unwrap(),
                schema.clone(),
                &req_env,
            ),
            Ok(TimedResult { result: true, .. })
        );

        let ps_new = PolicySet::from_str(
            r#"
        permit(
      principal,
      action in [Action::"action"],
      resource
    ) when {
      ((true && (a::"..."["r"])) && true) && true
    };"#,
        )
        .unwrap();

        assert_matches!(
            ffi.run_check_equivalent_with_cex_timed(&ps, &ps_new, schema.clone(), &req_env),
            Ok(TimedResult {
                result: Some(_),
                ..
            })
        );
        assert_matches!(
            ffi.run_check_equivalent_timed(&ps, &ps_new, schema.clone(), &req_env),
            Ok(TimedResult { result: false, .. })
        );

        assert_matches!(
            ffi.run_check_implies_with_cex_timed(&ps, &ps_new, schema.clone(), &req_env),
            Ok(TimedResult {
                result: Some(_),
                ..
            })
        );
        assert_matches!(
            ffi.run_check_implies_timed(&ps, &ps_new, schema.clone(), &req_env),
            Ok(TimedResult { result: false, .. })
        );

        assert_matches!(
            ffi.run_check_disjoint_with_cex_timed(&ps, &ps_new, schema.clone(), &req_env),
            Ok(TimedResult {
                result: Some(_),
                ..
            })
        );
        assert_matches!(
            ffi.run_check_disjoint_timed(&ps, &ps_new, schema, &req_env),
            Ok(TimedResult { result: false, .. })
        );
    }

    #[test]
    fn test_batched_evaluation() {
        let schema = Schema::from_str(
            r#"
            namespace Taxpreparer {
  type orgInfo = {
    organization: String,
    serviceline: String,
    location: String,
  };
  // A tax-preparing professional
  entity Professional = {
    assigned_orgs: Set<orgInfo>,
    location: String,
  };
  // A client's tax document
  entity Document = {
    serviceline: String,
    location: String,
    owner: Client,
  };
  // A client
  entity Client = {
    organization: String
  };

  action viewDocument appliesTo {
    principal: [Professional],
    resource: [Document],
  };
}
        "#,
        )
        .expect("valid schema");
        let policy = PolicySet::from_str(
            r#"
        // Rule 1a: organization-level access
permit (
  principal,
  action == Taxpreparer::Action::"viewDocument",
  resource
)
when
{
  principal.assigned_orgs
    .contains
    (
      {organization
       :resource.owner.organization,
       serviceline
       :resource.serviceline,
       location
       :resource.location}
    )
};
        "#,
        )
        .expect("valid policy");
        let entities = Entities::from_json_value(
            serde_json::json!([
                {
                    "uid": {
                        "type": "Taxpreparer::Professional",
                        "id": "Alice"
                    },
                    "attrs": {
                        "location": "IAD",
                        "assigned_orgs": [
                            {
                                "organization": "org-1",
                                "serviceline": "corporate",
                                "location": "IAD"
                            }
                        ]
                    },
                    "parents": []
                },
                {
                    "uid": {
                        "type": "Taxpreparer::Professional",
                        "id": "Bob"
                    },
                    "attrs": {
                        "location": "JFK",
                        "assigned_orgs": [
                            {
                                "organization": "org-1",
                                "serviceline": "corporate",
                                "location": "JFK"
                            }
                        ]
                    },
                    "parents": []
                },
                {
                    "uid": {
                        "type": "Taxpreparer::Client",
                        "id": "Ramon"
                    },
                    "attrs": {
                        "organization": "org-1"
                    },
                    "parents": []
                },
                {
                    "uid": {
                        "type": "Taxpreparer::Document",
                        "id": "ABC"
                    },
                    "attrs": {
                        "serviceline": "corporate",
                        "location": "IAD",
                        "owner": {
                            "type": "Taxpreparer::Client",
                            "id": "Ramon"
                        }
                    },
                    "parents": []
                },
                {
                    "uid": {
                        "type": "Taxpreparer::Document",
                        "id": "DEF"
                    },
                    "attrs": {
                        "serviceline": "corporate",
                        "location": "JFK",
                        "owner": {
                            "type": "Taxpreparer::Client",
                            "id": "Ramon"
                        }
                    },
                    "parents": []
                }
            ]),
            Some(&schema),
        )
        .expect("valid entities");
        let request = Request::new(
            "Taxpreparer::Professional::\"Alice\"".parse().unwrap(),
            "Taxpreparer::Action::\"viewDocument\"".parse().unwrap(),
            "Taxpreparer::Document::\"ABC\"".parse().unwrap(),
            Context::empty(),
            None,
        )
        .expect("valid request");
        let ffi = CedarLeanFfi::new();
        let response = ffi
            .batched_authorization(&policy, &schema, &request, &entities, 3)
            .unwrap();
        assert_eq!(response.decision, Some(cedar_policy::Decision::Allow));
    }

    #[test]
    fn empty_record_encoding() {
        let schema = Schema::from_str(
            r#"
            entity V;
entity N;
entity V3 = {
  "x": {}
};
action "" appliesTo {
  principal: [N],
  resource: [V],
  context: {}
};
            "#,
        )
        .unwrap();
        let pset = PolicySet::from_str(
            r#"
            permit(
  principal,
  action in [Action::""],
  resource
) when {
  {} == (V3::"".x)
};
            "#,
        )
        .unwrap();
        let request_env = request_env("N", "Action::\"\"", "V");
        let ffi = CedarLeanFfi::new();
        assert!(
            !ffi.run_check_always_denies(
                &pset,
                ffi.load_lean_schema_object(&schema).unwrap(),
                &request_env
            )
            .unwrap()
        );
    }

    /// Cross-language proto roundtrip: `Rust encode -> Lean decode -> Lean encode
    /// -> Rust decode` must preserve a `PolicySet`.
    ///
    /// This exercises the Lean codec on both sides — `CedarProto` decoding and
    /// `CedarProto.Encode.encodePolicies` re-encoding, including the scope-constraint
    /// paths (`==` / `in` / `is` / `is .. in`) that a bare-expr encoder can't reach.
    /// We compare two *decode outputs* (`reference` = Rust's own decode of its
    /// encoding, `actual` = Rust's decode of the Lean roundtrip). Comparing decode
    /// outputs cancels benign representation choices (e.g. `action in Action::"a"`
    /// vs `action in [Action::"a"]`, or how empty conditions render) so the assertion
    /// isolates genuine Lean encode/decode infidelities. Comparison is by the
    /// id-independent multiset of `Policy` display strings.
    mod proto_roundtrip {
        use super::{Policy, PolicyId, PolicySet, Schema};
        use crate::CedarLeanFfi;
        use arbitrary::Unstructured;
        use cedar_policy::proto::traits::Protobuf;
        use cedar_policy_generators::{
            schema::Schema as GenSchema, schema_gen::SchemaGen, settings::ABACSettings,
        };
        use proptest::prelude::*;

        /// One shared FFI handle for all proptest cases: the Lean runtime is
        /// thread-bound and its `Drop` finalizes the thread, so we init once
        /// (never dropped) rather than churning init/finalize per case.
        fn shared_ffi() -> &'static CedarLeanFfi {
            static FFI: std::sync::OnceLock<CedarLeanFfi> = std::sync::OnceLock::new();
            FFI.get_or_init(CedarLeanFfi::new)
        }

        /// DIAGNOSTIC: drive the welltyped-policy generator via FFI (Lean-encode), then
        /// Rust-DECODE the bytes and strict-validate. The Lean PBT proves the *original*
        /// policies are 100% well-typed, so any Rust rejection here is introduced by the
        /// Lean-encode → Rust-decode roundtrip. Dump the first ~10 failing (decoded) policies
        /// + the decoded schema's declared entity types + the strict errors, so we can compare
        /// against the Lean originals (same seeds) and localize the corruption.
        ///   cargo test -p cedar-lean-ffi dump_illtyped_roundtrip -- --ignored --nocapture
        #[test]
        #[ignore]
        fn dump_illtyped_roundtrip() {
            use cedar_policy::{ValidationMode, Validator};
            fn ru32(b: &[u8], p: usize) -> (usize, usize) {
                (u32::from_le_bytes([b[p], b[p + 1], b[p + 2], b[p + 3]]) as usize, p + 4)
            }
            let ffi = shared_ffi();
            let mut found = 0;
            'outer: for seed in 0..8u64 {
                let params = serde_json::json!({
                    "seed": seed, "size": 12, "schema_size": 12,
                    "strategy": "welltyped-policy", "count": 60
                });
                let buf = ffi.generate_schema_typeof_proto(&params).expect("ffi generate");
                let (slen, mut pos) = ru32(&buf, 0);
                let schema = match Schema::decode(&buf[pos..pos + slen]) { Ok(s) => s, Err(_) => continue };
                pos += slen;
                // Decoded schema's declared entity types (Debug shows the full schema).
                let schema_dbg = format!("{schema:?}");
                let (cnt, np0) = ru32(&buf, pos); pos = np0;
                for idx in 0..cnt {
                    let (plen, np) = ru32(&buf, pos); pos = np;
                    let ps = match PolicySet::decode(&buf[pos..pos + plen]) { Ok(p) => p, Err(_) => { pos += plen; continue } };
                    pos += plen;
                    let res = Validator::new(schema.clone()).validate(&ps, ValidationMode::Strict);
                    if !res.validation_passed() {
                        let errs: Vec<String> = res.validation_errors().map(|e| e.to_string()).collect();
                        eprintln!("=== FAIL seed={seed} idx={idx} (#{found}) ===");
                        eprintln!("  DECODED POLICY: {ps}");
                        eprintln!("  ERRORS: {errs:?}");
                        if found == 0 { eprintln!("  DECODED SCHEMA (seed {seed}): {schema_dbg}"); }
                        found += 1;
                        if found >= 10 { break 'outer; }
                    }
                }
            }
            eprintln!("\n=== shown {found} failing (decoded) policies ===");
        }

        /// Same generator settings the validation DRT fuzz targets use.
        fn settings() -> ABACSettings {
            ABACSettings {
                enable_additional_attributes: true,
                ..ABACSettings::type_directed()
            }
        }

        /// Drive `cedar-policy-generators` (the same infra the DRT fuzzers use) from a
        /// random byte buffer to produce a schema + a policy over it, converted to the
        /// public `cedar_policy` API types. Returns `None` when the generator runs out
        /// of entropy or the schema/policy can't be converted — those cases are skipped,
        /// not failures.
        fn generate(buf: &[u8]) -> Option<(Schema, PolicySet)> {
            let mut u = Unstructured::new(buf);
            let gen_schema = GenSchema::arbitrary(settings(), &mut u).ok()?;
            let hierarchy = gen_schema.arbitrary_hierarchy(&mut u).ok()?;
            // Static policy only: the Lean `encodePolicies` doesn't model template slots.
            let policy = gen_schema
                .arbitrary_static_policy(&hierarchy, &mut u)
                .ok()?;
            let schema = Schema::try_from(gen_schema).ok()?;
            let policyset = policy.into_policy_set();
            Some((schema, policyset))
        }

        /// Canonicalize a schema for order-insensitive comparison. `ValidatorSchema`'s
        /// `PartialEq` treats several repeated fields (notably enum choices, stored as an
        /// ordered `NonEmpty`) as ordered, but the Lean spec models them as *sets* and so
        /// re-emits them sorted. We compare via the protobuf model with every order-
        /// insensitive repeated field sorted; its `map` fields (attributes/context)
        /// already compare order-independently.
        fn schema_canon(
            vs: &cedar_policy_core::validator::ValidatorSchema,
        ) -> cedar_policy::proto::models::Schema {
            let mut m = cedar_policy::proto::models::Schema::from(vs);
            // These repeated fields are sets in the Lean model (ancestors/descendants,
            // enum choices, applies-to types), so sort AND dedup: Lean re-emits them as
            // sorted, duplicate-free sets, while cedar keeps declaration order/dups.
            for e in &mut m.entity_decls {
                e.descendants.sort_by_key(|n| format!("{n:?}"));
                e.descendants.dedup();
                e.enum_choices.sort();
                e.enum_choices.dedup();
            }
            m.entity_decls.sort_by_key(|e| format!("{:?}", e.name));
            for a in &mut m.action_decls {
                a.descendants.sort_by_key(|u| format!("{u:?}"));
                a.descendants.dedup();
                a.principal_types.sort_by_key(|n| format!("{n:?}"));
                a.principal_types.dedup();
                a.resource_types.sort_by_key(|n| format!("{n:?}"));
                a.resource_types.dedup();
            }
            m.action_decls.sort_by_key(|a| format!("{:?}", a.name));
            m
        }

        /// Id-independent structural fingerprint: sorted `Policy` display strings
        /// with annotation lines stripped. Cedar's `Display` omits the policy id but
        /// renders annotations as leading `@name("...")` lines; the Lean spec doesn't
        /// model annotations (they're authorization-irrelevant metadata), so we compare
        /// over the annotation-free policy — the part the Lean codec can preserve.
        fn fingerprint(ps: &PolicySet) -> Vec<String> {
            let mut v: Vec<String> = ps
                .policies()
                .map(|p| {
                    p.to_string()
                        .lines()
                        .filter(|l| !l.trim_start().starts_with('@'))
                        .collect::<Vec<_>>()
                        .join("\n")
                })
                .collect();
            v.sort();
            v
        }

        /// Roundtrip one static policy and assert the Lean codec preserved it.
        fn assert_roundtrip(ffi: &CedarLeanFfi, src: &str) {
            let mut pset = PolicySet::new();
            let pol = Policy::parse(Some(PolicyId::new("policy0")), src)
                .unwrap_or_else(|e| panic!("policy should parse: {src}: {e}"));
            pset.add(pol).unwrap();
            let bytes0 = pset.encode();
            let reference = PolicySet::decode(&bytes0[..]).unwrap();
            let lean_bytes = ffi.roundtrip_policyset_proto(&bytes0).unwrap();
            assert!(
                !lean_bytes.is_empty(),
                "Lean returned empty bytes for {src}"
            );
            let actual = PolicySet::decode(&lean_bytes[..]).unwrap();
            assert_eq!(
                fingerprint(&reference),
                fingerprint(&actual),
                "mismatch for {src}"
            );
        }

        /// Deterministic exhaustive sweep of every scope-constraint form (the code
        /// Diagnostic: decode a corpus batch from S3 and count slots / annotations /
        /// templates in the policies each arm actually generated. Confirms whether the
        /// slots-off arm really produced slot-free policies.
        #[test]
        #[ignore]
        fn inspect_corpus_batches() {
            for arm in ["r2_hw-slots-off", "r2_hw-slots-on", "hw-slots-off_late", "hw-slots-on_late", "wt-policy-sz12"] {
                let data = match std::fs::read(format!("/tmp/l4res/{arm}.bin")) {
                    Ok(d) => d,
                    Err(_) => { eprintln!("{arm}: no batch file"); continue; }
                };
                let (mut pos, mut n, mut slots, mut annots, mut templates, mut multi) = (0usize, 0u32, 0u32, 0u32, 0u32, 0u32);
                while pos + 4 <= data.len() {
                    let len = u32::from_le_bytes([data[pos], data[pos+1], data[pos+2], data[pos+3]]) as usize;
                    pos += 4;
                    if pos + len > data.len() { break; }
                    let rec = &data[pos..pos+len];
                    pos += len;
                    if rec.len() < 4 { continue; }
                    let sl = u32::from_le_bytes([rec[0], rec[1], rec[2], rec[3]]) as usize;
                    if 4 + sl > rec.len() { continue; }
                    if let Ok(ps) = PolicySet::decode(&rec[4+sl..]) {
                        n += 1;
                        if ps.templates().count() > 0 { templates += 1; }
                        if ps.policies().count() + ps.templates().count() > 1 { multi += 1; }
                        // definitive slot check: any template with >=1 slot
                        if ps.templates().any(|t| t.slots().count() > 0) { slots += 1; }
                        let s = ps.to_string();
                        if s.contains('@') { annots += 1; }
                    }
                }
                eprintln!("{arm:<16} inputs={n:<7} with_slots={slots:<6} with_annotations={annots:<6} with_template={templates:<6} multi_policy={multi}");
            }
        }

        /// Tabulate which scope-constraint FORMS each corpus actually emits, to check the
        /// welltyped-policy generator captures the full grammar (any/==/in/is/is..in for
        /// principal & resource; any/==/in/in[list] for action).
        #[test]
        #[ignore]
        fn scope_form_distribution() {
            use cedar_policy::{ActionConstraint, PrincipalConstraint, ResourceConstraint};
            for arm in ["wt-policy-sz12", "hw-slots-off", "hw-slots-off_late", "hw-slots-on_late"] {
                let data = match std::fs::read(format!("/tmp/l4res/{arm}.bin")) {
                    Ok(d) => d,
                    Err(_) => continue,
                };
                // principal: any,eq,in,is,ismem ; action: any,eq,in1,inN ; resource: any,eq,in,is,ismem
                let (mut p, mut a, mut r) = ([0u64; 5], [0u64; 4], [0u64; 5]);
                let (mut pos, mut n) = (0usize, 0u64);
                while pos + 4 <= data.len() {
                    let len = u32::from_le_bytes([data[pos], data[pos+1], data[pos+2], data[pos+3]]) as usize;
                    pos += 4;
                    if pos + len > data.len() { break; }
                    let rec = &data[pos..pos+len];
                    pos += len;
                    if rec.len() < 4 { continue; }
                    let sl = u32::from_le_bytes([rec[0], rec[1], rec[2], rec[3]]) as usize;
                    if 4 + sl > rec.len() { continue; }
                    if let Ok(ps) = PolicySet::decode(&rec[4+sl..]) {
                        for pol in ps.policies() {
                            n += 1;
                            match pol.principal_constraint() {
                                PrincipalConstraint::Any => p[0] += 1,
                                PrincipalConstraint::Eq(_) => p[1] += 1,
                                PrincipalConstraint::In(_) => p[2] += 1,
                                PrincipalConstraint::Is(_) => p[3] += 1,
                                PrincipalConstraint::IsIn(_, _) => p[4] += 1,
                            }
                            match pol.action_constraint() {
                                ActionConstraint::Any => a[0] += 1,
                                ActionConstraint::Eq(_) => a[1] += 1,
                                ActionConstraint::In(v) if v.len() == 1 => a[2] += 1,
                                ActionConstraint::In(_) => a[3] += 1,
                            }
                            match pol.resource_constraint() {
                                ResourceConstraint::Any => r[0] += 1,
                                ResourceConstraint::Eq(_) => r[1] += 1,
                                ResourceConstraint::In(_) => r[2] += 1,
                                ResourceConstraint::Is(_) => r[3] += 1,
                                ResourceConstraint::IsIn(_, _) => r[4] += 1,
                            }
                        }
                    }
                }
                eprintln!("== {arm} (n={n}) ==");
                eprintln!("  principal any={} ==={} in={} is={} is..in={}", p[0], p[1], p[2], p[3], p[4]);
                eprintln!("  action    any={} ==={} in={} in[list]={}", a[0], a[1], a[2], a[3]);
                eprintln!("  resource  any={} ==={} in={} is={} is..in={}", r[0], r[1], r[2], r[3], r[4]);
            }
        }

        /// Count `when`/`unless` clauses per policy in the specimen corpus — tests whether
        /// the generator asks for MULTIPLE conditions (each a separate HasType search).
        #[test]
        #[ignore]
        fn condition_clause_count() {
            for arm in ["wt-policy-sz12"] {
                let data = match std::fs::read(format!("/tmp/l4res/{arm}.bin")) { Ok(d)=>d, Err(_)=>continue };
                let mut hist = std::collections::BTreeMap::new();
                let (mut pos, mut n, mut total_clauses) = (0usize, 0u64, 0u64);
                while pos + 4 <= data.len() {
                    let len = u32::from_le_bytes([data[pos],data[pos+1],data[pos+2],data[pos+3]]) as usize;
                    pos += 4; if pos+len > data.len() { break; }
                    let rec=&data[pos..pos+len]; pos+=len;
                    if rec.len()<4 { continue; }
                    let sl=u32::from_le_bytes([rec[0],rec[1],rec[2],rec[3]]) as usize;
                    if 4+sl>rec.len() { continue; }
                    if let Ok(ps)=PolicySet::decode(&rec[4+sl..]) {
                        for pol in ps.policies() {
                            n+=1;
                            let s=pol.to_string();
                            let c = s.matches("when {").count() + s.matches("unless {").count();
                            *hist.entry(c).or_insert(0u64)+=1;
                            total_clauses += c as u64;
                        }
                    }
                }
                eprintln!("== {arm}: {n} policies, avg clauses/policy = {:.2} ==", total_clauses as f64 / n.max(1) as f64);
                for (c,cnt) in &hist { eprintln!("     {c} clause(s): {cnt} policies"); }
            }
        }

        /// Tally extension-function usage per corpus (which generator emits more extensions,
        /// and which specific functions), to explain the extension coverage residual.
        #[test]
        #[ignore]
        fn extension_usage() {
            let fns = [
                "decimal(", "ip(", "datetime(", "duration(",
                ".isIpv4(", ".isIpv6(", ".isLoopback(", ".isMulticast(", ".isInRange(",
                ".lessThan(", ".lessThanOrEqual(", ".greaterThan(", ".greaterThanOrEqual(",
                ".offset(", ".durationSince(", ".toDate(", ".toTime(",
                ".toMilliseconds(", ".toSeconds(", ".toMinutes(", ".toHours(", ".toDays(",
            ];
            for arm in ["wt-policy-sz12", "hw-slots-off_late", "hw-slots-on_late"] {
                let data = match std::fs::read(format!("/tmp/l4res/{arm}.bin")) { Ok(d)=>d, Err(_)=>continue };
                let mut counts = std::collections::BTreeMap::new();
                let (mut pos, mut n, mut with_ext) = (0usize, 0u64, 0u64);
                while pos + 4 <= data.len() {
                    let len = u32::from_le_bytes([data[pos],data[pos+1],data[pos+2],data[pos+3]]) as usize;
                    pos += 4;
                    if pos+len > data.len() { break; }
                    let rec=&data[pos..pos+len]; pos+=len;
                    if rec.len()<4 { continue; }
                    let sl=u32::from_le_bytes([rec[0],rec[1],rec[2],rec[3]]) as usize;
                    if 4+sl>rec.len() { continue; }
                    if let Ok(ps)=PolicySet::decode(&rec[4+sl..]) {
                        n+=1;
                        let s=ps.to_string();
                        let mut any=false;
                        for f in fns { let c=s.matches(f).count(); if c>0 { *counts.entry(f).or_insert(0u64)+=c as u64; any=true; } }
                        if any { with_ext+=1; }
                    }
                }
                eprintln!("== {arm}: {n} policies, {with_ext} use >=1 extension ==");
                for (f, c) in &counts {
                    eprintln!("     {f:<22} {c}");
                }
            }
        }

        /// Probe: after decode, is a static policy reconstructed as a `Template` (which
        /// eagerly builds an EST lossless -> exercises `est/*`) or a static `Policy`
        /// (Empty lossless -> no `est/*`)? Compare Rust-encoded vs Lean-encoded corpora.
        #[test]
        fn est_probe_templates_vs_policies() {
            let mut pset = PolicySet::new();
            pset.add(
                Policy::parse(
                    Some(PolicyId::new("policy0")),
                    "permit(principal == User::\"a\", action, resource) when { true };",
                )
                .unwrap(),
            )
            .unwrap();
            let rust_bytes = pset.encode();
            let rust_dec = PolicySet::decode(&rust_bytes[..]).unwrap();
            let lean_bytes = shared_ffi().roundtrip_policyset_proto(&rust_bytes).unwrap();
            let lean_dec = PolicySet::decode(&lean_bytes[..]).unwrap();
            eprintln!(
                "RUST-encoded decode: templates={} policies={}",
                rust_dec.templates().count(),
                rust_dec.policies().count()
            );
            eprintln!(
                "LEAN-encoded decode: templates={} policies={}",
                lean_dec.templates().count(),
                lean_dec.policies().count()
            );
        }

        /// paths added in `CedarProto.Encode`), with and without a `when` clause.
        #[test]
        fn sweep_scopes() {
            let principals = [
                "principal",
                "principal == User::\"a\"",
                "principal in Group::\"g\"",
                "principal is User",
                "principal is User in Group::\"g\"",
            ];
            let actions = [
                "action",
                "action == Action::\"view\"",
                "action in Action::\"a\"",
                "action in [Action::\"a\", Action::\"b\"]",
            ];
            let resources = [
                "resource",
                "resource == Photo::\"p\"",
                "resource in Album::\"al\"",
                "resource is Photo",
                "resource is Photo in Album::\"al\"",
            ];
            let ffi = shared_ffi();
            for p in principals {
                for a in actions {
                    for r in resources {
                        for cond in ["", " when { principal == resource }"] {
                            assert_roundtrip(ffi, &format!("permit({p}, {a}, {r}){cond};"));
                        }
                    }
                }
            }
        }

        proptest! {
            // A random byte buffer drives the generator; 4 KiB is enough entropy for a
            // schema + a policy while keeping most cases productive (few skips).
            #![proptest_config(ProptestConfig::with_cases(2000))]

            /// Policy-set proto roundtrip over randomly generated policies.
            #[test]
            fn policyset_proto_roundtrip(buf in prop::collection::vec(any::<u8>(), 512..4096)) {
                let Some((_schema, pset)) = generate(&buf) else {
                    return Ok(()); // not enough entropy this case; skip
                };
                let bytes0 = pset.encode();
                let reference = PolicySet::decode(&bytes0[..])
                    .expect("Rust should decode its own PolicySet encoding");

                let ffi = shared_ffi();
                let lean_bytes = ffi
                    .roundtrip_policyset_proto(&bytes0)
                    .expect("Lean roundtrip FFI call should succeed");
                prop_assert!(
                    !lean_bytes.is_empty(),
                    "Lean returned empty bytes (decode/link failed) for policies:\n{pset}"
                );
                let actual = PolicySet::decode(&lean_bytes[..])
                    .expect("Rust should decode the Lean-re-encoded PolicySet");

                prop_assert_eq!(
                    fingerprint(&reference),
                    fingerprint(&actual),
                    "PolicySet changed across the Lean proto roundtrip for policies:\n{}",
                    pset
                );
            }

            /// Schema proto roundtrip over randomly generated schemas. Compares the
            /// two decode outputs as `ValidatorSchema`s (order-independent `PartialEq`).
            #[test]
            fn schema_proto_roundtrip(buf in prop::collection::vec(any::<u8>(), 512..4096)) {
                use cedar_policy_core::validator::ValidatorSchema;
                let Some((schema, _pset)) = generate(&buf) else {
                    return Ok(()); // not enough entropy this case; skip
                };
                let bytes0 = schema.encode();
                let reference = Schema::decode(&bytes0[..])
                    .expect("Rust should decode its own Schema encoding");

                let ffi = shared_ffi();
                let lean_bytes = ffi
                    .roundtrip_schema_proto(&bytes0)
                    .expect("Lean schema roundtrip FFI call should succeed");
                prop_assert!(
                    !lean_bytes.is_empty(),
                    "Lean returned empty bytes (schema decode failed)"
                );
                let actual = Schema::decode(&lean_bytes[..])
                    .expect("Rust should decode the Lean-re-encoded Schema");

                let r: &ValidatorSchema = reference.as_ref();
                let a: &ValidatorSchema = actual.as_ref();
                if schema_canon(r) != schema_canon(a) {
                    let rc = schema_canon(r);
                    let ac = schema_canon(a);
                    eprintln!("=== SCHEMA MISMATCH ===");
                    for e in &rc.entity_decls {
                        eprintln!("REF entity {:?} descendants={:?} enum={:?} attrs={:?} tags={}",
                            e.name, e.descendants, e.enum_choices,
                            e.attributes.keys().collect::<Vec<_>>(), e.tags.is_some());
                    }
                    for e in &ac.entity_decls {
                        eprintln!("ACT entity {:?} descendants={:?} enum={:?} attrs={:?} tags={}",
                            e.name, e.descendants, e.enum_choices,
                            e.attributes.keys().collect::<Vec<_>>(), e.tags.is_some());
                    }
                    for a2 in &rc.action_decls {
                        eprintln!("REF action {:?} desc={:?} p={:?} r={:?}",
                            a2.name, a2.descendants, a2.principal_types, a2.resource_types);
                    }
                    for a2 in &ac.action_decls {
                        eprintln!("ACT action {:?} desc={:?} p={:?} r={:?}",
                            a2.name, a2.descendants, a2.principal_types, a2.resource_types);
                    }
                }
                prop_assert!(
                    schema_canon(r) == schema_canon(a),
                    "Schema changed across the Lean proto roundtrip"
                );
            }
        }
    }
}
