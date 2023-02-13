# Running Flux

You can run `flux` on a single file or entire crate.

## Running on a File: `rustc-flux`

You can use `rustc-flux` as you would use `rustc`.
For example, the following command checks the file `test.rs`.

```bash
rustc-flux path/to/test.rs
```

The flux binary accepts the same flags as rustc.
You could for example check a file as a library instead of a binary like so

```bash
rustc-flux --crate-type=lib path/to/test.rs
```

## Running on a Crate: `cargo-flux`

You can use `cargo-flux` as you would use `cargo`. For the most part this means
instead of running `cargo check`, you should run

``` bash
cargo-flux check
```

in order to get `flux` to check your code.

## Developing locally

You can set the `FLUX_DRIVER_PATH` environment variable to `./target/debug/flux-driver` if you
want `cargo-flux` and `rustc-flux` to use the version of `flux-driver` that is built
when you run `cargo build`. This is useful if you want to run `cargo build` instead
of `cargo install --path flux` every time you make a change.

## A tiny example

The following example declares a function `inc`
that returns an integer greater than the input.
We use the nightly feature `register_tool`
to register the `flux` tool in order to
add refinement annotations to functions.

```rust
#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x: i32) -> i32{v: x < v})]
pub fn inc(x: i32) -> i32 {
    x - 1
}
```

You can save the above snippet in say `test0.rs` and then run

```bash
rustc-flux --crate-type=lib path/to/test0.rs
```

you should see in your output

```text
error[FLUX]: postcondition might not hold
 --> test0.rs:6:5
  |
6 |     x - 1
  |     ^^^^^
```

as indeed `x - 1` is *not* greater than `x` as required by the output refinement `i32{v: x < v}`.

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
hassle you should never execute it directly.  Instead, use `rustc-flux` or `cargo-flux`.

## Editor Support

This section assumes you have installed `flux`, `cargo-flux`, and `rustc-flux`.

### Rust-Analyzer in VSCode

Add this to the workspace settings i.e. `.vscode/settings.json`

```json
{
  "rust-analyzer.check.overrideCommand": [
    "cargo-flux",
    "check",
    "--workspace",
    "--message-format=json"
  ]
}
```

If you want to change the `flux-driver` used by `cargo-flux`, then also specify the
`FLUX_PATH` like in the example below, which uses the version generated when you
run `cargo build`.

``` json
{
  "rust-analyzer.check.extraEnv": {
    "FLUX_DRIVER_PATH": "/path/to/flux-repo/target/debug/flux-driver",
  }
}
```

**Note:** Make sure to edit the paths in the above snippet to point to the correct locations on your machine.

## Configuration

### Environment Variables

You can set various `env` variables to customize the behavior of `flux`.

* `FLUX_CONFIG` tells `flux` where to find a config file for these settings.
  * By default, `flux` searches its directory for a `flux.toml` or `.flux.toml`.
* `FLUX_DRIVER_PATH=path/to/flux-driver` tells `cargo-flux` and `rustc-flux` where to find the `flux` binary.
  * Defaults to the default `flux-driver` installation (typically found in `~/.cargo/bin`).
* `FLUX_LOG_DIR=path/to/log/` with default `./log/`
* `FLUX_DUMP_CONSTRAINT=1` sets the directory where constraints, timing and cache are saved.
* `FLUX_DUMP_CHECKER_TRACE=1` saves the checker's trace (useful for debugging!)
* `FLUX_DUMP_TIMINGS=1` saves the profile information
* `FLUX_DUMP_MIR=1` saves the low-level MIR for each analyzed function
* `FLUX_POINTER_WIDTH=N` the size of (either `32` or `64`), used to determine if an integer cast is lossy (default `64`).
* `FLUX_CHECK_DEF=name` only checks definitions containing `name` as a substring
* `FLUX_CACHE=1"` switches on query caching and saves the cache in `FLUX_CACHE_FILE`
* `FLUX_CACHE_FILE=file.json` customizes the cache file, default `FLUX_LOG_DIR/cache.json`

### Config file

The config file is a `.toml` file that contains on each line the lowercase name
of a `flux` command line flag without the `FLUX_` prefix. Set environment
variables take priority over the config file.

The config file should be in the project root.

For example, suppose your project root contains the following `flux.toml`.

```toml
log_dir = "./test"
dump_timings = true
dump_mir = true
```

and you run in the project root

```bash
FLUX_DUMP_MIR=0 cargo-flux check
```

then `flux` will create the directory `./test/` and write `./test/timings`, a file
containing profiling information. It will _not_ dump the MIR because that setting
was overridden by setting the environment variable `FLUX_DUMP_MIR=0`.

### Query Caching

`FLUX_CACHE=1` persistently caches the safe fixpoint queries for each `DefId` in
`FLUX_LOG_DIR/FLUX_CACHE_FILE`, and on subsequent runs, skips queries that are
already in the cache, which considerably speeds up `cargo-flux check` on an
entire crate.
