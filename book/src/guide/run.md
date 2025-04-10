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

### Environment Variables

You can set various `env` variables to customize the behavior of `flux`.

- `FLUX_CONFIG` tells `flux` where to find a config file for these settings.
  - By default, `flux` searches its directory for a `flux.toml` or `.flux.toml`.
- `FLUX_LOG_DIR=path/to/log/` sets the directory where constraints, timing and cache are saved. Defaults to `./log/`.
- `FLUX_DUMP_CONSTRAINT=1` tell `flux` to dump constraints generated for each function.
- `FLUX_DUMP_CHECKER_TRACE=1` saves the checker's trace (useful for debugging!)
- `FLUX_DUMP_MIR=1` saves the low-level MIR for each analyzed function
- `FLUX_POINTER_WIDTH=N` the size of (either `32` or `64`), used to determine if an integer cast is lossy (default `64`).
- `FLUX_CHECK_DEF=name` only checks definitions containing `name` as a substring
- `FLUX_CHECK_FILES=/absolute/path/to/file1.rs,/absolute/path/to/file2.rs` only checks the specified files
- `FLUX_CACHE=1"` switches on query caching and saves the cache in `FLUX_CACHE_FILE`
- `FLUX_CACHE_FILE=file.json` customizes the cache file, default `FLUX_LOG_DIR/cache.json`
- `FLUX_CHECK_OVERFLOW=1` checks for over and underflow on arithmetic integer
  operations, default `0`. When set to `0`, it still checks for underflow on
  unsigned integer subtraction.
- `FLUX_SOLVER=z3` Can be either `z3` or `cvc5`.
- `FLUX_SMT_DEFINE_FUN=1` translates _monomorphic_ `defs` functions into SMT `define-fun` instead of inlining them away inside `flux`.
- `FLUX_STATS=1` Compute statistics about number and size of annotations. Dumps a file per crate to `FLUX_LOG_DIR`.

### Config file

The config file is a `.toml` file that contains on each line the lowercase name
of a `flux` command line flag without the `FLUX_` prefix. Set environment
variables take priority over the config file.

The config file should be in the project root.

For example, suppose your project root contains the following `flux.toml`.

```toml
log_dir = "./log_dir"
dump_mir = true
cache = true
```

and you run in the project root

```bash
FLUX_DUMP_MIR=1 cargo flux check
```

then `flux` will create the directory `./log_dir/` and dump mir bodies inside.

### Crate Config

Some flags can be configured on a per-crate basis using the custom inner attribute `#![flux_rs::cfg]`.
This annotation relies on the unstable custom inner attributes feature. To be able to use with a
non-nightly compiler you have to put it under a `cfg_attr`.
For example, to enable overflow checking:

```rust
#![cfg_attr(flux, flux_rs::cfg(check_overflow = true))]
```

The only flag supported now is overflow checking.

### Query Caching

`FLUX_CACHE=1` persistently caches the safe fixpoint queries for each `DefId` in
`FLUX_LOG_DIR/FLUX_CACHE_FILE`, and on subsequent runs, skips queries that are
already in the cache, which considerably speeds up `cargo-flux check` on an
entire crate.
