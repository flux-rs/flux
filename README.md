# LiquidRust


## Requirements

* [rustup](https://rustup.rs/)
* [liquid-fixpoint](https://github.com/ucsd-progsys/liquid-fixpoint)
* [z3](https://github.com/Z3Prover/z3)

Be sure that the `liquid-fixpoint` and `z3` executables are in your $PATH.

## Build Instructions

The only way to test LiquidRust is to build it from source.

First you need to clone this repository

```bash
git clone https://github.com/liquid-rust/liquid-rust
cd liquid-rust
```

To build the source you need a nightly version of rustc.
We pin the version using a [toolchain file](/rust-toolchain) (more info [here](https://rust-lang.github.io/rustup/overrides.html#the-toolchain-file)).
If you are using rustup, no special action is needed as it should install the correct rustc version and components based on the information on that file.

Finally, build the project using `cargo`

```bash
cargo build
```

## Usage

### liquid-rust binary

You can run the liquid-rust binary with `cargo run`.
The liquid-rust binary is a [rustc driver](https://rustc-dev-guide.rust-lang.org/rustc-driver.html?highlight=driver#the-rustc-driver-and-interface) (similar to how clippy works) meaning it uses rustc as a library to "drive" compilation performing aditional analysis along the way.
In practice this means you could use liquid-rust as you would use rustc.
For example, the following command checks the file `test.rs` (everythins after the `--` are the arguments to the liquid-rust binary)

```bash
cargo run -- path/to/test.rs
```

The liquid-rust binary accepts the same flags than rustc.
You could for example check a file as a library instead of a binary like so

```bash
cargo run -- --crate-type=lib
```

Additionally, at the moment liquid-rust passes some default flags (like `-O` and `-Cpanic=abort`) because otherwise the resulting mir will have features
not yet supported.

### A tiny example

The following example declares a funcion `inc` that returns a integer greater than the input.
We use the nightly feature `register_tool` to register the `lr` tool in order to add refinement annotations to functions.

```rust
#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty("fn<n: int>(i32@n) -> i32{v: v > n}")]
pub fn inc(x: i32) -> i32 {
    x + 1
}
```

## Limitations

This is a prototype! Use at your own risk. Everything could break and it will break.
