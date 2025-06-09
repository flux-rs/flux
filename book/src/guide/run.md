# Running Flux

You can run `flux` on a single file or entire crate.

## Running on a File: `flux`

You can use `flux` as you would use `rustc`.
For example, the following command checks the file `test.rs`.

```bash
flux path/to/test.rs
```

The flux binary accepts the same flags as `rustc`.
You could for example check a file as a library instead of a binary like so

```bash
flux --crate-type=lib path/to/test.rs
```

### Refinement Annotations on a File

When running flux on a file with `flux path/to/test.rs`, refinement annotations should be prefixed with `flux::`.

For example, the refinement below will only work when running `flux` which is intended for use on a single file.

```rust
#[flux::sig(fn(x: i32) -> i32{v: x < v})]
fn inc(x: i32) -> i32 {
    x - 1
}
```

## Running on a package: `cargo-flux`

Flux is integrated with `cargo` and can be invoked in a package as follows:

```bash
cargo flux
```

By default, Flux won't verify a package unless it's explicitly enabled in the manifest.
To do so add the following to `Cargo.toml`:

```toml
[package.metadata.flux]
enabled = true
```

### Refinement Annotations on a Cargo Projects

Adding refinement annotations to cargo projects is simple. You can add `flux-rs` as a dependency in `Cargo.toml`

```toml
[dependencies]
flux-rs = { git  = "https://github.com/flux-rs/flux.git" }
```

Then, import attributes from `flux_rs` and add the appropriate refinement annoations.

```rust
use flux_rs::*;

#[sig(fn(x: i32) -> i32{v: x < v)]
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
#[flux::sig(fn(x: i32) -> i32{v: x < v})]
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

### Flux Flags

The `flux` binary accepts configuration flags in the format `-Fname=value`. For boolean flags, the
`value` can be one of `y`, `yes`, `on`, `true`, `n`, `no`, `off`, `false`. Alternatively, the `value`
can be omitted which will default to `true`. For example, to set the solver to `cvc5` and enable
qualifier scrapping:

```console
flux -Fsolver=cvc5 -Fscrape-quals path/to/file.rs
```

For all available flags, see <https://flux-rs.github.io/flux/doc/flux_config/flags/struct.Flags.html>

### Cargo Projects

When working with a Cargo project, some of the [flags](#Flux-Flags) can be configured in the
`[package.metadata.flux]` table in `Cargo.toml`. For example, to enable query caching and set
`cvc5` as the solver:

```toml
# Cargo.toml
[package.metadata.flux]
enabled = true
cache = true
solver = "cvc5"
```

Additionally, `cargo flux` searches for a configuration file called `flux.toml` with the same format
as the metadata table. The content of `flux.toml` takes precedence and it's merged with the
content of the `metadata` table. Note that the content of `flux.toml` will override the `metadata`
for all crates, including dependencies. This behavior is likely to change in the future as we figure
out what configurations make sense to have per package and which should only affect the current execution
of `cargo flux`.

You can see the format of the `metadata` in <https://flux-rs.github.io/flux/doc/flux_bin/struct.FluxMetadata.html>.

### `FLUXFLAGS` Environement Variable

When running `cargo flux`, flags defined in `FLUXFLAGS` will be passed to all `flux` invocations,
for example, to print timing information for all crates checked by Flux:

```console
FLUXFLAGS="-Ftimings" cargo flux
```
