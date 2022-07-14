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


## RJ Notes

- default_fn_sig
- refine_fn_sig

https://internals.rust-lang.org/t/accessing-the-defid-of-a-trait-implementation/17001


`with_self_ty` takes a `PolyFnSig` aka `Binder<T>` and replaces it by plugging in the `Self`

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/sty/struct.Binder.html#method.with_self_ty-1

and produces a `PolyTraitRef` which you can then get a `DefId` from?

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/sty/type.PolyTraitRef.html


What does this do?

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.try_expand_impl_trait_type


impl_item_implementor_ids

aha. see notes for

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.impl_item_implementor_ids

All implementations of a trait!

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.find_map_relevant_impl


https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.implementations_of_trait


method-`DefId`
-----> impl-`DefId`  (using `impl_of_method`)
-----> trait-`DefId` (using `trait_id_of_impl`)


START with a method-`DefId`

**Step 1**

```rust
pub fn impl_of_method(self, def_id: DefId) -> Option<DefId>
```

If the given DefId describes a method belonging to an impl, returns the DefId of the impl that the method belongs to; otherwise, returns None.




```rust
pub fn trait_id_of_impl(self, def_id: DefId) -> Option<DefId>
```

Given the DefId of an impl, returns the DefId of the trait it implements. If it implements no trait, returns None.
source



Complete Reference to a Trait

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/sty/struct.TraitRef.html

Pair of

- `DefId`    (the trait)
- `SubstRef` (the "args")


### Nico Route (to avoid `key` shenanigan)

* stash the `rustc` Subst at the call-site (during lowering)

* `self_ty`  for `find_map_relevant_impl` is the `0` elem of the `subst`

* `trait_f` --?-> `trait_id` ---use find_map_relevant_impl--> `impl_id` --?-> `impl_f`

`impl_id` + `trait_f` -> `impl_f` via `impl_item_implementor_ids`


HOW TO get from `trait_f` to `trait_id` ?

trait_of_item