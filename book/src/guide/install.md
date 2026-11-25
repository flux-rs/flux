# Installing and Running Flux

You can install and then run Flux either on a single file or on an entire crate.

## Requirements

- [rustup](https://rustup.rs/)

  Rustup is required because Flux needs access to the source code of the Rust compiler, which we grab from rustup.

- [liquid-fixpoint](https://github.com/ucsd-progsys/liquid-fixpoint) and
  [z3](https://github.com/Z3Prover/z3) 4.15 or later

  The [installation step](#install) downloads both for you on the platforms with prebuilt binaries:
  x86_64 Linux, aarch64 macOS, and x86_64 Windows. On other platforms, install them yourself:
  [build liquid-fixpoint from source](https://github.com/ucsd-progsys/liquid-fixpoint?tab=readme-ov-file#how-to-build-and-install)
  and download z3 from [Z3 GitHub Releases](https://github.com/Z3Prover/z3/releases). Make sure that
  the `fixpoint` and `z3` binaries are in your `$PATH`.

## Install

The only way to use Flux is to build it from source.

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

This will install the Flux sysroot (the binaries and precompiled libraries) to `$HOME/.flux/sysroot` and
link two binaries, `flux` and `cargo-flux`, from your cargo home (`$HOME/.cargo/bin`). These two binaries
should be used respectively to run Flux on either a single file or on a project using cargo.

With `--bundle-solvers`, the installation also downloads liquid-fixpoint and z3 into the sysroot if
there are prebuilt binaries for your platform. Flux looks up any solver that isn't downloaded in your
`$PATH`.

## Flux Home

The Flux home is the directory `$HOME/.flux`. Its location can be changed by setting the
`FLUX_HOME` environment variable. It contains:

- `config.toml` — Your personal [configuration](../reference/config.md), which applies to every
  invocation of `cargo flux`. It is never modified by Flux.
- `sysroot/` — The Flux sysroot. It contains the binaries (`bin/flux`, `bin/cargo-flux` and
  `bin/flux-driver`), the precompiled Flux libraries (`lib/`), and a manifest (`sysroot.toml`)
  recording the Flux version and the Rust toolchain it was built with. It is managed by
  `cargo xtask install` and `cargo xtask uninstall`, which replace or remove the whole directory.
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

## A note about the flux-driver binary

The `flux-driver` binary is a [rustc
driver](https://rustc-dev-guide.rust-lang.org/rustc-driver.html?highlight=driver#the-rustc-driver-and-interface)
(similar to how clippy works) meaning it uses rustc as a library to "drive"
compilation performing additional analysis along the way. Running the binary
requires dynamically linking a correct version of `librustc`. Thus, to avoid the
hassle you should never execute it directly. Instead, use `flux` or `cargo-flux`.

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

**Note:** Make sure to edit the paths in the above snippet to point to the correct locations on your machine.

## Configuration

A package is configured in two places:

- The `[package.metadata.flux]` table in `Cargo.toml` describes properties of the crate, i.e.,
  _what_ is verified. See [The Manifest Format](../reference/manifest.md).
- `.flux/config.toml` files control _how_ `cargo flux` runs, e.g., caching, timeouts or extra
  output. See [Configuration](../reference/config.md).

### Flux Flags

Under the hood, Flux is controlled by flags of the form `-Fname=value`. For boolean flags, `value`
can be one of `y`, `yes`, `on`, `true`, `n`, `no`, `off`, `false`, or be omitted, which means
`true`. For all available flags, see
<https://flux-rs.github.io/flux/doc/flux_config/flags/struct.Flags.html>.

With `cargo flux`, you rarely need to pass flags yourself. Set them where they belong instead, and
`cargo flux` translates them into flags for each package:

- Properties of the crate, e.g., the solver, go in its manifest:

  ```toml
  [package.metadata.flux]
  enabled = true
  solver = "cvc5"
  scrape-quals = true
  ```

- How Flux runs, e.g., timeouts or extra output, goes in `.flux/config.toml`, either in your project
  or in `~/.flux/config.toml` for all your projects:

  ```toml
  [fixpoint]
  timeout = 30

  [stats]
  timings = true
  ```

For a one-off run, you can still pass flags on the command line, or in the `FLUXFLAGS` environment
variable:

```console
cargo flux --Ftimings
FLUXFLAGS="-Ftimings" cargo flux
```

See [how flags are combined](../reference/config.md#how-flags-are-combined) for how these sources
interact.

When running `flux` on a single file, which doesn't read the manifest or the configuration files,
pass the flags directly:

```console
flux -Fsolver=cvc5 -Fscrape-quals path/to/file.rs
```

### Verbose Output

One particularly useful setting is

```toml
[diagnostics]
verbose = true
```

or `--Fflux-verbose` for a single run. It makes Flux print the name of each function as it checks
it, along with more detailed error messages. This is helpful when Flux hits an internal error (ICE):
you can see _which_ function caused it, mark it as `trusted` so Flux skips checking its body, and
live to fight another day.
