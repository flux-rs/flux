# Installing and Running Flux

You can install and then run Flux either on a single file or on an entire crate.

## Requirements

- [rustup](https://rustup.rs/)

  Flux runs with a specific nightly version of Rust, which the installation installs with rustup.

- [liquid-fixpoint](https://github.com/ucsd-progsys/liquid-fixpoint) and
  [z3](https://github.com/Z3Prover/z3) 4.15 or later

  The prebuilt releases include both. If a bundled solver doesn't run on your machine, e.g., on an
  older OS, the installation removes it and Flux looks it up in your `$PATH`. When you build Flux
  from source, `--bundle-solvers` downloads both on the platforms with prebuilt binaries. On other
  platforms, install them yourself:
  [build liquid-fixpoint from source](https://github.com/ucsd-progsys/liquid-fixpoint?tab=readme-ov-file#how-to-build-and-install)
  and download z3 from [Z3 GitHub Releases](https://github.com/Z3Prover/z3/releases). Make sure that
  the `fixpoint` and `z3` binaries are in your `$PATH`.

## Install

There are prebuilt releases of Flux for x86_64 Linux, aarch64 macOS, and x86_64 Windows. On other
platforms, [build Flux from source](#building-from-source).

On Linux and macOS, run

```bash
curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/flux-rs/flux/main/install.sh | sh
```

On Windows, run the following in PowerShell

```powershell
irm https://raw.githubusercontent.com/flux-rs/flux/main/install.ps1 | iex
```

This installs the latest release of Flux: the Flux sysroot (the binaries, precompiled libraries,
and solvers) to `$HOME/.flux/sysroot`, and the Rust toolchain it needs with rustup. It also links
two binaries, `flux` and `cargo-flux`, from your cargo home (`$HOME/.cargo/bin`). These two binaries
should be used respectively to run Flux on either a single file or on a cargo project.

### Updating and Uninstalling

To update Flux to the latest release, run

```bash
cargo flux self update
```

A release is published for every commit to the `main` branch. A copy of the latest one is kept for
each day as `nightly-yyyy-mm-dd`, for the last 30 days. To install one of them, e.g., to go back to a
version that worked for you, run

```bash
cargo flux self update --to nightly-2026-11-20
```

To uninstall Flux, run `cargo flux self uninstall`. This leaves your
[configuration](#flux-home) and the Rust toolchain alone.

### Building from Source

First you need to clone the repository

```bash
git clone https://github.com/flux-rs/flux
cd flux
```

Flux is built with a specific nightly version of Rust, pinned in the repository's
[toolchain file](https://github.com/flux-rs/flux/blob/main/rust-toolchain.toml). You don't need to
install it yourself: `rustup`
[reads that file](https://rust-lang.github.io/rustup/overrides.html#the-toolchain-file) and installs
that version, together with the components Flux needs, the first time you build.

Next, run the following to build and install `flux` binaries

```bash
cargo xtask install --bundle-solvers
```

This installs Flux like the prebuilt releases do. With `--bundle-solvers`, the installation also
downloads liquid-fixpoint and z3 into the sysroot if there are prebuilt binaries for your platform.
Flux looks up any solver that isn't downloaded in your `$PATH`. Run `cargo xtask uninstall` to
uninstall it.

## Flux Home

The Flux home is the directory `$HOME/.flux`. Its location can be changed by setting the
`FLUX_HOME` environment variable. It contains:

- `config.toml` — Your personal [configuration](../reference/config.md), which applies to every
  invocation of `cargo flux`. It is never modified by Flux.
- `sysroot/` — The Flux sysroot. It contains the binaries (`bin/flux`, `bin/cargo-flux` and
  `bin/flux-driver`), the precompiled Flux libraries (`lib/`), and a manifest (`sysroot.toml`)
  recording the Flux version and the Rust toolchain it was built with. It is managed by
  `cargo flux self` and `cargo xtask install`, which replace or remove the whole directory.
  Use the `FLUX_SYSROOT` environment variable to use a sysroot in a different location.

## Running on a package: `cargo-flux`

The most common way to use Flux is to run it on a Cargo package.
This allows you to check an entire crate in one command, `cargo flux`.

### Step 1: Install Flux

[Install Flux](#install) as described above.

### Step 2: Enable Flux for the Package

By default, Flux won't verify a package unless it's explicitly enabled in the manifest.
To do so add the following to `Cargo.toml`:

```toml
[package.metadata.flux]
enabled = true
```

Now you can run `cargo flux` to check the package.

### Step 3: Enable Refinement Attributes

In step 2, you will likely get some refinement errors, and to remove
those you will need to add some refinement annotations to your code.
To do so, add the following to your `Cargo.toml`, which
adds the procedural macros Flux uses to your project

```toml
[dependencies]
flux-rs = { git  = "https://github.com/flux-rs/flux.git" }
```

Then, import attributes from `flux_rs` and add the appropriate refinement annotations.

```rust
use flux_rs::attrs::*;

#[spec(fn(x: i32) -> i32{v: x < v})]
fn inc(x: i32) -> i32 {
    x - 1
}
```

## Running on a File: `flux`

You can use `flux` as you would use `rustc`.
For example, the following command checks the file `test.rs`.

```bash
flux path/to/test.rs
```

The flux binary accepts the same flags as `rustc`.
You could for example check a file as a library
instead of a binary like so

```bash
flux --crate-type=lib path/to/test.rs
```

### Refinement Annotations on a File

When running flux on a file with `flux path/to/test.rs`, refinement annotations should be prefixed with `flux::`.

For example, the refinement below will only work when running `flux` which is intended for use on a single file.

```rust
#[flux::spec(fn(x: i32) -> i32{v: x < v})]
fn inc(x: i32) -> i32 {
    x - 1
}
```

## A tiny example

The following example declares a function `inc`
that returns an integer greater than the input.
We use the nightly feature `register_tool`
to register the `flux` tool in order to
add refinement annotations to functions.

```rust
#[flux::spec(fn(x: i32) -> i32{v: x < v})]
pub fn inc(x: i32) -> i32 {
    x - 1
}
```

You can save the above snippet in say `test0.rs` and then run

```bash
flux --crate-type=lib path/to/test0.rs
```

you should see in your output

```text
error[FLUX]: postcondition might not hold
 --> test0.rs:3:5
  |
3 |     x - 1
  |     ^^^^^
```

as indeed `x - 1` is _not_ greater than `x` as required by the output refinement `i32{v: x < v}`.

If you fix the error by replacing `x - 1` with `x + 1`, you should get no errors
in the output (the output may be empty, but in this case no output is a good
thing).

Read [these chapters](SUMMARY.md#learn) to learn more about what you specify and verify with `flux`.

## Configuration

A package is configured in two places:

- The `[package.metadata.flux]` table in `Cargo.toml` describes properties of the crate, i.e.,
  _what_ is verified. See [The Manifest Format](../reference/manifest.md).
- `.flux/config.toml` files control _how_ `cargo flux` runs, e.g., caching, timeouts or extra
  output. See [Configuration](../reference/config.md).

## Editor Support

This section assumes you have installed `cargo-flux`.

### Rust-Analyzer in VSCode

Add this to the workspace settings i.e. `.vscode/settings.json`

```json
{
  "rust-analyzer.check.overrideCommand": [
    "cargo",
    "flux",
    "--workspace",
    "--message-format=json-diagnostic-rendered-ansi"
  ]
}
```
