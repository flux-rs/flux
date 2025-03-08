# Installing Flux

## Requirements

- [rustup](https://rustup.rs/)
- [liquid-fixpoint](https://github.com/ucsd-progsys/liquid-fixpoint)
- [z3](https://github.com/Z3Prover/z3)

Be sure that the `liquid-fixpoint` and `z3` executables are in your `$PATH`.

## Installing

The only way to use Flux is to build it from source.

First you need to clone the repository

```bash
git clone https://github.com/flux-rs/flux
cd flux
```

To build the source you need a nightly version of `rustc`.
We pin the version using a [toolchain file](https://github.com/flux-rs/flux/blob/main/rust-toolchain) (more info [here](https://rust-lang.github.io/rustup/overrides.html#the-toolchain-file)).
If you are using `rustup`, no special action is needed as it should install the correct `rustc` version and components based on the information on that file.

Next, run the following to build and install `flux` binaries

```bash
cargo xtask install
```

This will install two binaries `flux` and `cargo-flux` in your cargo home. These two binaries should be used
respectively to run Flux on either a single file or on a project using cargo. The installation process will
also copy some files to `$HOME/.flux`.

In order to use Flux refinement attributes in a Cargo project, you will need to add the
following to your Cargo.toml

```toml
[dependencies]
flux-rs = { git  = "https://github.com/flux-rs/flux.git" }
```

This will add the procedural macros Flux uses to your project; it is not a susbstitute
for installing Flux, which must still be done.
