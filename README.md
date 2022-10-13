# Flux

## Requirements

- [rustup](https://rustup.rs/)
- [liquid-fixpoint](https://github.com/ucsd-progsys/liquid-fixpoint)
- [z3](https://github.com/Z3Prover/z3)

Be sure that the `liquid-fixpoint` and `z3` executables are in your $PATH.

## Build Instructions

The only way to test Flux is to build it from source.

First you need to clone this repository

```bash
git clone https://github.com/liquid-rust/flux
cd flux
```

To build the source you need a nightly version of rustc.
We pin the version using a [toolchain file](/rust-toolchain) (more info [here](https://rust-lang.github.io/rustup/overrides.html#the-toolchain-file)).
If you are using rustup, no special action is needed as it should install the correct rustc version and components based on the information on that file.

Finally, build the project using `cargo`

```bash
cargo build
```

## Usage

### flux binary

You can run the flux binary with `cargo run`.
The flux binary is a [rustc driver](https://rustc-dev-guide.rust-lang.org/rustc-driver.html?highlight=driver#the-rustc-driver-and-interface) (similar to how clippy works) meaning it uses rustc as a library to "drive" compilation performing aditional analysis along the way.
In practice this means you can use flux as you would use rustc.
For example, the following command checks the file `test.rs` (everythins after the `--` are the arguments to the flux binary)

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

### flux.sh

To run `flux` on code outside the repo, use script in `tools/flux.sh`

- copy it to some place on your `$PATH`
- edit the variable `FLUX` to point to the root of your local `flux` repo. 


### A tiny example

The following example declares a funcion `inc` that returns a integer greater than the input.
We use the nightly feature `register_tool` to register the `lr` tool in order to add refinement annotations to functions.

```rust
#![feature(register_tool)]
#![register_tool(flux)]

#[flux::ty(fn<n: int>(i32@n) -> i32{v: v > n})]
pub fn inc(x: i32) -> i32 {
    x + 1
}
```

You can save the above snippet in say `test0.rs` and then run

```
cargo run -- --crate-type=lib path/to/test0.rs
```

and you should get some output like

```
Ok(FixpointResult { tag: Safe })
```

## Test

You can run the various tests in the `tests/pos` and `tests/neg` directory using

```
$ cargo test -p flux-tests
```

## Limitations

This is a prototype! Use at your own risk. Everything could break and it will break.


## Rust-Analyzer in VSCode

Add this to the workspace settings popping in the appropriate paths for 

* `DYLD_FALLBACK_LIBRARY_PATH` 
* `RUSTC_WRAPPER` 
* `RUSTUP_TOOLCHAIN`

```
{
  "rust-analyzer.checkOnSave.overrideCommand": [
    "env",
    "DYLD_FALLBACK_LIBRARY_PATH=/Users/rjhala/.rustup/toolchains/nightly-2022-08-02-x86_64-apple-darwin/lib",
    "RUSTC_WRAPPER=/Users/rjhala/research/rust/flux/target/debug/flux",
    "RUSTUP_TOOLCHAIN=nightly-2022-08-02",
    "cargo",
    "check",
    "--message-format=json"
  ],
  "spellright.language": [
    "en"
  ],
  "spellright.documentTypes": [
    "latex",
    "plaintext"
  ]
}
```
