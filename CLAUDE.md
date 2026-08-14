# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Flux is a refinement type checker for Rust. It extends Rust's type system with logical predicates that are verified using SMT solvers (Z3 via liquid-fixpoint).

## Build Commands

```bash
# Run regression tests (builds flux-driver and sysroot automatically)
cargo xtask test [filter]         # filter is optional substring match

# Run flux on a single file
cargo xtask run <file.rs>
cargo xtask run file.rs -- -Zdump-mir=ghost  # with extra flags

# Expand macros (e.g., extern_spec)
cargo xtask expand <file.rs>

# Install binaries to ~/.cargo/bin and libs to ~/.flux
cargo xtask install               # release profile (default)
cargo xtask install --profile dev # dev profile with debug info

# Rebuild library artifacts (flux-core, flux-rs, etc.)
cargo xtask build-sysroot

# Format and lint
cargo fmt --check
cargo clippy
```

## Testing

Tests are in `tests/tests/`:
- `pos/` - tests that should pass type checking
- `neg/` - tests that should fail (expected errors in `.stderr` files)
- `lib/` - auxiliary library code for other tests
- `todo/` - known failing tests

Run specific tests: `cargo xtask test impl_trait` runs all tests containing "impl_trait".

## Architecture

Flux is a rustc [compiler driver](https://rustc-dev-guide.rust-lang.org/rustc-driver.html) that hooks into compilation via the `Callbacks` trait.

### Crate Structure

**Compiler crates** (`crates/`):
- `flux-driver` - Main entry point, rustc callbacks
- `flux-syntax` - LALRPOP-based parser for surface syntax
- `flux-desugar` - Desugars surface syntax to FHIR
- `flux-middle` - Core types: `fhir` and `rty` IRs (like `rustc_middle`)
- `flux-fhir-analysis` - FHIR analysis, conversion to `rty`
- `flux-refineck` - Refinement type checker (main analysis)
- `flux-infer` - Type/refinement inference
- `flux-bin` - CLI wrappers (`flux`, `cargo-flux`)

**Library crates** (`lib/`):
- `flux-rs` - User-facing macros and attributes
- `flux-core` - Extern specs for stdlib
- `liquid-fixpoint` - SMT solver interface

### Intermediate Representations

```
Surface → FHIR → rty
 (parse)  (desugar) (convert)
```

- **Surface** (`flux-syntax`): Source-level annotations
- **FHIR** (`flux-middle::fhir`): Flux High-Level IR, analogous to rustc's HIR
- **rty** (`flux-middle::rty`): Refined types, analogous to `rustc_middle::ty`

### Compilation Flow

1. Rustc calls `FluxCallbacks` during compilation
2. Flux parses `#[flux::sig(...)]` annotations (flux-syntax)
3. Desugars to FHIR with explicit refinement parameters (flux-desugar)
4. Converts to rty (flux-fhir-analysis)
5. Refinement type checking generates SMT queries (flux-refineck)
6. Queries sent to Z3 via liquid-fixpoint

## Debugging

```bash
# Enable backtraces with source spans
cargo xtask install --profile dev
RUST_BACKTRACE=1 cargo xtask run test.rs

# Show where errors are emitted
cargo xtask run test.rs  # automatically includes -Ztrack-diagnostics

# Dump MIR for inspection
cargo xtask run test.rs -- -Zdump-mir=ghost

# Dump checker trace
FLUX_DUMP_CHECKER_TRACE=1 FLUX_CHECK_DEF=fn_name cargo flux
python3 tools/logreader.py

# Catch panics and continue (for exploring new codebases)
FLUX_CATCH_BUGS=1 cargo flux
```

## Code Conventions

**Bug reporting in code** - use these instead of `panic!`:
- `QueryErr::bug` - when returning `QueryResult`
- `span_bug!` - when you have a `Span`
- `tracked_span_bug!` - uses thread-local span
- `bug!` - fallback with nice formatting

**DefId handling** - clippy is configured to disallow direct `DefId::is_local`, `DefId::expect_local`, `DefId::as_local`. Use `MaybeExternId` or `ResolvedDefId` instead to properly handle extern specs.

## Requirements

- Nightly rustc (pinned in `rust-toolchain`)
- [liquid-fixpoint](https://github.com/ucsd-progsys/liquid-fixpoint) binary in PATH
- [Z3](https://github.com/Z3Prover/z3) 4.15+ in PATH
