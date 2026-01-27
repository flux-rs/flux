# Flux Repository - Copilot Coding Agent Instructions

## Overview

Flux is a refinement type checker for Rust. This is a Rust workspace with multiple crates, requiring specific dependencies (Z3, fixpoint) and custom build tooling through `cargo xtask`.

**Languages & Frameworks:** Rust (edition 2024), custom rustc integration  
**Repository Size:** ~15 crates in workspace + 4 library packages + test suites

**Note:** Required dependencies (fixpoint and Z3 4.12.1) are automatically installed in the Copilot coding agent environment via `.github/workflows/copilot-setup-steps.yml`. For local development, developers need to install these dependencies manually (see CI workflow for installation steps).

## Build & Test Instructions

### Test Commands

1. **Run all regression tests**:
   ```bash
   cargo xtask test
   ```
   This runs tests from `tests/pos/` (should pass) and `tests/neg/` (should fail with specific errors)

2. **Run specific tests** (filtered by substring):
   ```bash
   cargo xtask test <filter>
   # Example: cargo xtask test impl_trait
   ```

3. **Test on a single file**:
   ```bash
   cargo xtask run <file.rs>
   # Example: cargo xtask run tests/pos/surface/impl_trait00.rs
   ```
   This automatically sets up proper flags for Flux attributes and debugging

### Linting & Formatting

1. **Format code**:
   ```bash
   cargo fmt --check  # Check only
   cargo fmt          # Auto-format
   ```
   Uses `rustfmt.toml` configuration

2. **Run clippy**:
   ```bash
   cargo clippy
   ```
   Uses `clippy.toml` with custom lints defined in `Cargo.toml` workspace section

## Project Layout

### Directory Structure

```
/
├── crates/           - Main Flux implementation crates
│   ├── flux-bin/     - CLI binary (flux, cargo-flux)
│   ├── flux-driver/  - Rustc driver integration
│   ├── flux-middle/  - Core type system and refinement types
│   ├── flux-refineck/ - Refinement type checker
│   ├── flux-syntax/  - Parsing Flux surface syntax
│   ├── flux-errors/  - Error reporting
│   └── ...          - Other supporting crates
├── lib/             - User-facing Flux libraries
│   ├── flux-rs/     - Main library with macros (#[flux::sig], etc.)
│   ├── flux-core/   - Extern specs for std library
│   ├── flux-attrs/  - Attribute proc macros
│   └── flux-alloc/  - Extern specs for alloc
├── tests/           - Regression test suite
│   ├── pos/         - Tests that should type check
│   └── neg/         - Tests that should fail with errors
├── xtask/           - Build system implementation
├── book/            - User documentation (mdBook).
├── .github/
│   └── workflows/
│       ├── ci.yml   - Main CI: tests, vtock, lean-demo, rustfmt, clippy
│       └── ...
└── Configuration files (see below)
```

### Key Files

- **Cargo.toml**: Workspace configuration with all crates, dependencies, and lints
- **rust-toolchain.toml**: Specifies Rust toolchain (edition 2024, nightly features)
- **clippy.toml**: Clippy configuration (allowed/denied lints)
- **rustfmt.toml**: Code formatting rules
- **typos.toml**: Spell checking configuration
- **book/src/guide/develop.md**: Detailed developer guide

### Architecture Notes

- **Flux is a rustc driver**: It integrates with the Rust compiler as a custom driver
- **Two-stage execution**: 
  1. Build flux-driver and cargo-flux binaries
  2. Use cargo-flux to build libraries with refinement types
- **Custom test framework**: Uses `cargo xtask test` which invokes the test harness in `tests/` package

## CI Pipeline

The `.github/workflows/ci.yml` runs on push/PR to main:

1. **tests job**: Runs `cargo xtask test` on ubuntu/macos/windows
2. **vtock job**: Tests Flux on the Tock OS kernel (verification use case)
3. **lean-demo job**: Tests Flux-to-Lean translation feature
4. **rustfmt job**: Checks code formatting
5. **clippy job**: Runs `cargo check` and `cargo clippy`

All jobs (except formatting/clippy) require fixpoint and Z3 to be installed first. In the Copilot coding agent environment, these dependencies are automatically installed via `.github/workflows/copilot-setup-steps.yml`.

## Validation Steps

Before submitting changes:

1. **Format code**: `cargo fmt`
2. **Run regression tests**: `cargo xtask test`

## Important Conventions

- **Error reporting**: Use `bug!`, `span_bug!`, `tracked_span_bug!`, or `QueryErr::bug` for unreachable code paths
- **Debugging flags**: `-Ztrack-diagnostics=y` to show where errors are emitted (enabled by `cargo xtask run`)
- **Backtraces**: Set `RUST_BACKTRACE=1`; dev profile gives better traces

## Development Workflow

1. Make changes to relevant crates in `crates/` or `lib/`
2. Test specific functionality: `cargo xtask test <filter>`
3. Or test single file: `cargo xtask run <file.rs>`
4. Run formatter: `cargo fmt`
5. Run full test suite: `cargo xtask test`

## Trust These Instructions

The information above has been validated against the repository structure, CI configuration, and developer documentation. When you need to build, test, or understand Flux:

- **ALWAYS use `cargo xtask`** for building and testing
- **NEVER run `cargo test`** directly on the workspace
- Refer to these instructions first before searching the codebase for build/test commands
