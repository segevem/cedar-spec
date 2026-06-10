# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Cedar-spec is the formal specification of the [Cedar](https://github.com/cedar-policy/cedar) policy language. It contains:
- A Lean 4 formalization with verified proofs about Cedar's semantics
- Differential randomized testing (DRT) infrastructure that tests the Rust production implementation against the Lean spec
- Property-based testing (PBT) targets for the Rust implementation
- A CLI tool (`cedar-lean-cli`) that exposes the Lean formalization for authorization, validation, and analysis

## Build Commands

### Lean Formalization (cedar-lean/)

```bash
cd cedar-lean
lake update
lake build Cedar                    # Build proofs and definitions
lake build Cedar SymCC              # Build including symbolic compiler
lake exe CedarUnitTests             # Run unit tests
lake exe CedarSymTests              # Run symbolic compiler tests
lake lint                           # Check that Cedar.Thm imports all proof files
lake -R -Kenv=dev build Cedar:docs  # Build documentation (requires doc-gen4)
```

Static libraries for FFI (needed before building Rust DRT/CLI code):
```bash
cd cedar-lean
../cedar-drt/build_lean_lib.sh
# Equivalent to: lake build Cedar:static Protobuf:static CedarProto:static Cedar.SymCC:static CedarFFI:static Batteries:static
```

### DRT Framework (cedar-drt/)

Requires the `cedar` repo cloned at `./cedar` (sibling to cedar-lean, cedar-drt, etc.).

```bash
source cedar-drt/set_env_vars.sh        # Sets LEAN_LIB_DIR, LD_LIBRARY_PATH
cd cedar-drt
cargo build                             # Build the DRT library
cargo test                              # Run tests
cargo test --features "integration-testing"  # Run integration tests (requires cedar-integration-tests)
cargo fmt --all --check                 # Check formatting
```

Fuzz targets:
```bash
cd cedar-drt
cargo fuzz build -s none                # Build all fuzz targets
cargo fuzz run -s none <target>         # Run a specific fuzz target
cargo fuzz list                         # List available targets
```

### Cedar Lean CLI (cedar-lean-cli/)

```bash
source cedar-lean-ffi/set_env_vars.sh
cd cedar-lean-cli
cargo build
cargo test
cargo install --path .                  # Install the CLI binary
```

Uses insta for snapshot testing (`cargo insta review` to update snapshots).

### Cedar Policy Generators (cedar-policy-generators/)

```bash
cd cedar-policy-generators
cargo build
cargo test
cargo fmt --all --check
```

### Docker (full DRT environment)

```bash
docker build . -t cedar_drt
docker run --rm -it cedar_drt
```

## Architecture

### Lean Formalization (cedar-lean/Cedar/)

The formalization mirrors Cedar's structure:
- `Cedar/Spec/` — Definitional engine: `evaluate`, `satisfied`, `isAuthorized`
- `Cedar/Validation/` — Definitional validator: `typeOf`, `checkLevel`
- `Cedar/SymCC/` — Symbolic compiler: compiles expressions to SMT terms
- `Cedar/TPE/` — Trivial partial evaluation
- `Cedar/Thm/` — Verified theorems (authorization, slicing, typechecking, symbolic compilation)
- `Cedar/Data/` — Core data types (maps, sets, etc.)
- `CedarProto/` — Protobuf deserialization for Cedar types
- `CedarFFI/` — FFI entry points called from Rust via lean-sys
- `DiffTest/` — Diff test harness (Lean side)
- `SymTest/` — Symbolic compiler test harness

### DRT Infrastructure (cedar-drt/)

- `cedar-drt/src/` — Core DRT library: parsing utilities, test dumping, logging
- `cedar-drt/fuzz/` — All fuzz targets (separate Cargo crate `cedar-drt-inner`)
- `cedar-drt/fuzz/src/` — Shared fuzzing infrastructure
- `cedar-lean-ffi/` — Rust FFI bindings to call Lean code; uses protobuf for serialization between Rust and Lean

### Data Flow (DRT)

1. `cedar-policy-generators` generates random Cedar inputs (schemas, policies, entities, requests) via the `arbitrary` crate
2. Fuzz targets in `cedar-drt/fuzz/` send the same input to both:
   - The Rust production implementation (`cedar-policy` crate)
   - The Lean formalization (via `cedar-lean-ffi` → protobuf → `CedarFFI`)
3. Results are compared; mismatches are bugs

### Dependency Chain

`cedar-drt/fuzz` → `cedar-drt` → `cedar-lean-ffi` → (Lean static libs from `cedar-lean`)
                  → `cedar-policy-generators` → `cedar-policy` (from `./cedar/`)

The `[patch.crates-io]` sections in Cargo.toml files redirect cedar crate dependencies to the local `./cedar/` checkout.

## Lean Style Conventions

- Theorem names and `Prop` terms: `lower_snake_case`
- Types, structures, modules: `UpperCamelCase`
- Functions: `lowerCamelCase` (unless returning `Prop`, then `UpperCamelCase`)
- Use `simp only` instead of `simp` (except to close goals)
- Use `exact` over `apply` when possible
- Use `have` to deconstruct; `rcases` only for disjunctions
- Sort `import`/`open` statements lexicographically
- Main theorems need a `/-- ... -/` docstring

## Environment Requirements

- Lean toolchain: managed via `lean-toolchain` file (currently v4.29.1)
- `source cedar-drt/set_env_vars.sh` (or `cedar-lean-ffi/set_env_vars.sh`) must be run before building Rust code that links against Lean
- `protoc` must be installed for protobuf compilation
- `cvc5` (>= v1.0.5) required for symbolic compiler analysis; set `CVC5` env var to the executable path
- The `cedar` repo must be cloned at `./cedar` for DRT builds
