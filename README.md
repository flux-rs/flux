
![Flux](logo.png)

`flux` is a refinement type checker for Rust.

See the [blog](https://liquid-rust.github.io/) for details on refinement types and rust.

## Documentation

See the [docs](https://liquid-rust.github.io/flux/) for details on how to install and run.

## Requirements

- [rustup](https://rustup.rs/)
- [liquid-fixpoint](https://github.com/ucsd-progsys/liquid-fixpoint)
- [z3](https://github.com/Z3Prover/z3)

Be sure that the `liquid-fixpoint` and `z3` executables are in your $PATH.

## Installing

The only way to use `flux` is to build it from source.

First you need to clone this repository

```bash
git clone https://github.com/liquid-rust/flux
cd flux
```

To build the source you need a nightly version of rustc.
We pin the version using a [toolchain file](/rust-toolchain) (more info [here](https://rust-lang.github.io/rustup/overrides.html#the-toolchain-file)).
If you are using rustup, no special action is needed as it should install the correct rustc version and components based on the information on that file.

Next, install the `flux` binary using

```bash
cargo install --lib flux
```

Note that you should not call `flux` directly.

Finally, install `rustc-flux` and `cargo-flux` using

```bash
cargo install --lib flux-bin
```

## Usage

### `rustc-flux`

You can use `rustc-flux` as you would use `rustc`.
For example, the following command checks the file `test.rs`.

```bash
rustc-flux path/to/test.rs
```

The flux binary accepts the same flags than rustc.
You could for example check a file as a library instead of a binary like so

```bash
rustc-flux --crate-type=lib path/to/test.rs
```

Additionally, at the moment flux passes some default flags (like `-O` and
`-Cpanic=abort`) because otherwise the resulting mir will have features not yet
supported.

### `cargo-flux`

You can use `cargo-flux` as you would use `cargo`. For the most part this means
instead of running `cargo check`, you should run

``` bash
cargo-flux check
```

in order to get `flux` to check your code.

### `cargo run`

If you're developing in `flux` and want a quicker way to test your changes, you
can use `cargo run -- args` instead of `rustc-flux args`.

### A tiny example

The following example declares a funcion `inc` that returns a integer greater than the input.
We use the nightly feature `register_tool` to register the `flux` tool in order to add refinement annotations to functions.

```rust
#![feature(register_tool)]
#![register_tool(flux)]

#[flux::ty(fn(n: i32) -> i32{v: v > n})]
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

### A note about the flux binary

The flux binary is a [rustc
driver](https://rustc-dev-guide.rust-lang.org/rustc-driver.html?highlight=driver#the-rustc-driver-and-interface)
(similar to how clippy works) meaning it uses rustc as a library to "drive"
compilation performing aditional analysis along the way.  You should never
execute it on its own - it will probably fail with some ugly error message.
Instead, use `rustc-flux` or `cargo-flux`.


## Test

You can run the various tests in the `tests/pos` and `tests/neg` directory using

```
$ cargo test -p flux-tests
```

## Grammar of Refinements

Note: This changes frequently! For most up-to-date grammar see [`surface_grammar.lalrpop`](flux-syntax/src/surface_grammar.lalrpop)

```
e ::= n                     // numbers 1,2,3...
    | x                     // identifiers x,y,z...
    | x.f                   // index-field access
    | e + e                 // addition
    | e - e                 // subtraction
    | n * e                 // multiplication by constant
    | if p { e } else { e } // if-then-else
    | f(e...)               // uninterpreted function application

p ::= true | false
    | e = e   // equality
    | e < e   // less than
    | p || p  // disjunction
    | p && p  // conjunction
    | p => p  // implication
    | !p      // negation
```

## Limitations

This is a prototype! Use at your own risk. Everything could break and it will break.


## Rust-Analyzer in VSCode

Add this to the workspace settings i.e. `.vscode/settings.json` using in the appropriate paths for

* `DYLD_FALLBACK_LIBRARY_PATH` (on `macos`) or `LD_LIBRARY_PATH` (on `linux`)
* `RUSTC_WRAPPER` (should be `flux` if you have installed `flux`, but it can be any path to a `flux` binary, e.g. `./target/debug/flux` if you are testing changes to `flux`)
* `RUSTUP_TOOLCHAIN` (should be the same as the contents of `/path/to/flux/rust-toolchain.toml`)

```json
{
  "rust-analyzer.checkOnSave.extraEnv": {
    "RUSTC_WRAPPER": "flux",
    "RUSTUP_TOOLCHAIN": "nightly-2022-10-11",
    "LD_LIBRARY_PATH": "/path/to/.rustup/toolchains/nightly-2022-10-11-x86_64-apple-darwin/lib"
  }
}
```
