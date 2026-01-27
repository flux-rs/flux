# Flux Repository - Copilot Coding Agent Instructions

## Overview

Flux is a refinement type checker for Rust. This is a Rust workspace with multiple crates, requiring specific dependencies (Z3, fixpoint) and custom build tooling through `cargo xtask`.

**Languages & Frameworks:** Rust (edition 2024), custom rustc integration  
**Repository Size:** ~15 crates in workspace + 4 library packages + test suites

## Build & Test Instructions

### Prerequisites

Before building or testing, you MUST have the following dependencies installed:
- **fixpoint**: Use `.github/actions/install-fixpoint` action or install from https://github.com/ucsd-progsys/liquid-fixpoint
- **Z3 SMT solver**: Version 4.12.1 for regular tests, 4.15.3 for vtock/lean-demo tests
- **Rust toolchain**: Specified in `rust-toolchain.toml` (edition 2024)

### Build Commands

**IMPORTANT**: Always use `cargo xtask` (or `cargo x`) for building and testing. Do NOT use plain `cargo build` or `cargo test` directly on workspace crates as Flux requires special sysroot setup.

1. **Build Flux binary** (development):
   ```bash
   cargo xtask install --profile dev
   ```
   This installs flux binaries to `~/.cargo/bin` and precompiled libraries to `~/.flux`

2. **Build for release**:
   ```bash
   cargo xtask install --profile release
   ```

3. **Build sysroot only** (when modifying libraries):
   ```bash
   cargo xtask build-sysroot
   ```

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

3. **Check for typos**:
   ```bash
   # Configuration in typos.toml
   typos
   ```

### Common Issues & Workarounds

- **"Cannot find flux-driver"**: Run `cargo xtask build-sysroot` to rebuild the sysroot
- **Test timeout**: Some tests require Z3 4.15.3 (not 4.12.1) to avoid hanging
- **Library changes not reflected**: Force rebuild with `cargo xtask build-sysroot`
- **Tests failing after dependency changes**: Clean and rebuild with `cargo xtask install --profile dev`

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
│   ├── neg/         - Tests that should fail with errors
│   └── ui/          - UI tests
├── xtask/           - Build system implementation
├── book/            - User documentation (mdBook)
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
- **backtracetk.toml**: Backtrace configuration
- **NOTES.md**: Developer notes (measures, UIF, etc.)
- **book/src/guide/develop.md**: Detailed developer guide

### Architecture Notes

- **Flux is a rustc driver**: It integrates with the Rust compiler as a custom driver
- **Sysroot setup is required**: Libraries must be pre-compiled to `<repo>/sysroot/` (local dev/tests) or `~/.flux` (installed)
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

All jobs (except formatting/clippy) require fixpoint and Z3 to be installed first.

## Validation Steps

Before submitting changes:

1. **Format code**: `cargo fmt`
2. **Run clippy**: `cargo clippy` (should have no warnings)
3. **Run affected tests**: `cargo xtask test <filter>` for relevant test subsets
4. **Build documentation** (if docs changed): `cargo xtask doc`
5. **Verify library changes**: If you modified `lib/*`, run `cargo xtask build-sysroot` then re-test

## Important Conventions

- **Error reporting**: Use `bug!`, `span_bug!`, `tracked_span_bug!`, or `QueryErr::bug` for unreachable code paths
- **Debugging flags**: `-Ztrack-diagnostics=y` to show where errors are emitted (enabled by `cargo xtask run`)
- **MIR dumping**: Use `-Zdump-mir=<stage>` to dump MIR at different stages
- **Macro expansion**: Use `cargo xtask expand <file>` to see expanded code
- **Backtraces**: Set `RUST_BACKTRACE=1`; dev profile gives better traces
- **Library testing**: When changing lib/* crates, use `cargo xtask build-sysroot` to force rebuild

## Development Workflow

1. Make changes to relevant crates in `crates/` or `lib/`
2. If library changes: `cargo xtask build-sysroot`
3. Test specific functionality: `cargo xtask test <filter>`
4. Or test single file: `cargo xtask run <file.rs>`
5. Run formatter: `cargo fmt`
6. Run clippy: `cargo clippy`
7. Run full test suite: `cargo xtask test`

## Trust These Instructions

The information above has been validated against the repository structure, CI configuration, and developer documentation. When you need to build, test, or understand Flux:

- **ALWAYS use `cargo xtask`** for building and testing
- **NEVER run `cargo test`** directly on the workspace
- **ALWAYS rebuild sysroot** after library changes
- Refer to these instructions first before searching the codebase for build/test commands
