# Running Flux

The flux binary is a [rustc driver](https://rustc-dev-guide.rust-lang.org/rustc-driver.html?highlight=driver#the-rustc-driver-and-interface)
(similar to how clippy works) meaning it uses `rustc` as a library to "drive" compilation performing aditional analysis along the way.
In practice this means you can use flux as you would use rustc, typically in one of the following three ways.

## Running inside the `flux` source directory

If you are in the `flux/` source directory, you can run the flux binary with `cargo run`.

For example, the following command checks the file `test.rs` (everything after the `--` are the arguments to the flux binary)

```bash
cargo run -- path/to/test.rs
```

The flux binary accepts the same flags than rustc.

You could for example check a file as a library instead of a binary like so

```bash
cargo run -- --crate-type=lib path/to/test.rs
```

Additionally, at the moment flux passes some
default flags (like `-O` and `-Cpanic=abort`) because
otherwise the resulting mir will have features
not yet supported.

## Running outside the `flux` source directory

To run `flux` on code outside the repo, use the script in `tools/flux.sh`

- copy it to some place on your `$PATH`
- edit the variable `FLUX` to point to the root of your local `flux` repo.


## A tiny example

The following example declares a funcion `inc`
that returns a integer greater than the input.
We use the nightly feature `register_tool`
to register the `flux` tool in order to
add refinement annotations to functions.

```rust
#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x: i32) -> i32{v: x < v})]
pub fn inc(x: i32) -> i32 {
    x + 1
}
```

You can save the above snippet in say `test0.rs` and then run

```
$ flux.sh --crate-type=lib path/to/test0.rs
```

and you should get some output like

```
    Finished dev [unoptimized + debuginfo] target(s) in 0.14s
    Running `.../flux --crate-type=lib test0.rs`
```

If you edit the code to change `x + 1` to `x - 1` you should get an error like

```
error[FLUX]: postcondition might not hold
 --> test0.rs:6:5
  |
6 |     x - 1
  |     ^^^^^
```

as indeed `x - 1` is *not* greater than `x` as required by the output refinement `i32{v: x < v}`.

Read [these chapters](SUMMARY.md#learn) to learn more about what you specify and verify with `flux`.

## Cargo Wrapper

You can run `flux` on an entire crate by using the script `tools/cargo-flux` as described below.

```bash
#!/bin/bash

RUSTUP_TOOLCHAIN=nightly-2022-10-11 DYLD_FALLBACK_LIBRARY_PATH=~/.rustup/toolchains/nightly-2022-10-11-x86_64-apple-darwin/lib RUSTC_WRAPPER=/path/to/flux/target/debug/flux cargo $@
```

**Step 1**: Copy the above script to some place on your `$PATH` and rename it to `cargo-flux`.

**Step 2**: Edit the script to make sure the `RUSTUP_TOOLCHAIN` and `DYLD_FALLBACK_LIBRARY_PATH`
(or `LD_LIBRARY_PATH` on linux) point to the appropriate places on your machine.

**Step 3** Now you can run `cargo-flux check` (instead of `cargo check`) in the relevant crate directory.