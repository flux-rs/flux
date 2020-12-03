# Liquid Rust

## Requirements

- [rustup](https://rustup.rs/) (version 1.23.0 or later).
- [liquid-fixpoint](https://github.com/ucsd-progsys/liquid-fixpoint) (develop branch).
- [z3](https://github.com/Z3Prover/z3) (version 4.8.9 or later).

Be sure that the `liquid-fixpoint` executable is in your `$PATH`.

## Build instructions

The only way to use Liquid Rust right now is compiling it from source.

First you need to clone this repository
```bash
git clone https://github.com/christianpoveda/liquid-rust
cd liquid-rust
```
Then you can build the project using `cargo`:

```bash
cargo build
```

`rustup` will download the correct toolchain and compile the project.

## Usage

### Compiling files

You can use the `run.sh` script to compile any Rust source code file as you
would with `rustc`.

As an example, if you want to compile a file `foo.rs` as a library, you can
run:

```bash
./run.sh foo.rs --crate-type=lib
```

### A tiny example

The following example uses Liquid Rust to verify that the `inc` function always
returns an integer greater than the one received as parameter.

```rust
#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(x: usize) -> {y: usize | y > x}")]
pub fn inc(x: usize) -> usize {
    x + 1
}
```

## Limitations

This is a prototype! Most of the Rust features are not supported by Liquid
Rust. In particular you cannot use Liquid Rust if your programs contains:

- Types that are not integers, booleans or `()`.
- Loops.

Liquid Rust only supports release mode and the `run.sh` script will
automatically pass the `-O` flag to the compiler.
