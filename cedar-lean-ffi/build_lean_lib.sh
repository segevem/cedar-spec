#!/bin/bash
# Copyright Cedar Contributors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Build command needed for linking Lean lib with Rust code
cd ../cedar-lean/
lake update
# CedarGen:static is required because CedarFFI.Generate imports CedarGen relational
# generators (incl. the WellTypedPolicy generator in CedarGen.Relational.PolicyGen); the
# Rust FFI links `Cedar_CedarGen`, so its archive must be rebuilt alongside the others.
lake build Cedar:static Protobuf:static CedarProto:static Cedar.SymCC:static CedarFFI:static CedarGen:static Batteries:static