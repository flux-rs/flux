# Installing Flux

## Requirements

- [rustup](https://rustup.rs/)
- [liquid-fixpoint](https://github.com/ucsd-progsys/liquid-fixpoint)
- [z3](https://github.com/Z3Prover/z3)

Be sure that the `liquid-fixpoint` and `z3` executables are in your `$PATH`.

## Installing

The only way to use `flux` is to build it from source.

First you need to clone the repository

```bash
git clone https://github.com/flux-rs/flux
cd flux
```

To build the source you need a nightly version of `rustc`.
We pin the version using a [toolchain file](/rust-toolchain) (more info [here](https://rust-lang.github.io/rustup/overrides.html#the-toolchain-file)).
If you are using `rustup`, no special action is needed as it should install the correct `rustc` version and components based on the information on that file.

Next, run the following to build and install `flux` binaries

```bash
cargo xtask install
```

This will install `flux-driver`, `rustc-flux` and `cargo-flux`. Note that you should not call `flux-driver` directly, but rather use `rustc-flux` and `cargo-flux`.
