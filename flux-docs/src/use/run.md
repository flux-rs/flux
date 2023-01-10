# Running Flux

## `rustc-flux`

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

## `cargo-flux`

You can use `cargo-flux` as you would use `cargo`. For the most part this means
instead of running `cargo check`, you should run

``` bash
cargo-flux check
```

in order to get `flux` to check your code.

## Developing locally

You can set the `FLUX_PATH` environment variable to `./target/debug/flux` if you
want `cargo-flux` and `rustc-flux` to use the version of `flux` that is built when you run `cargo build`. This is useful if you want to run `cargo build` instead
of `cargo install --path flux` every time you make a change.

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
    x - 1
}
```

You can save the above snippet in say `test0.rs` and then run

```
$ rustc-flux --crate-type=lib path/to/test0.rs
```

you should see in your output

```
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

## A note about the flux binary

The flux binary is a [rustc
driver](https://rustc-dev-guide.rust-lang.org/rustc-driver.html?highlight=driver#the-rustc-driver-and-interface)
(similar to how clippy works) meaning it uses rustc as a library to "drive"
compilation performing aditional analysis along the way.  You should never
execute it on its own - it will probably fail with some ugly error message.
Instead, use `rustc-flux` or `cargo-flux`.
