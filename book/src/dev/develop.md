# Developer's Guide

## Regression Tests

You can run the various regression tests in the `tests/pos` and `tests/neg` directories using
`cargo xtask test`

This will build the flux binary and then run it against the entire test suite.
You can optionally pass a _filter_ to only run tests containing some substring.
For example:

```console
$ cargo xtask test impl_trait
   Compiling xtask v0.1.0 (/path/to/flux/xtask)
    Finished dev [unoptimized + debuginfo] target(s) in 0.29s
     Running `target/debug/xtask test impl_trait`
$ cargo build
    Finished dev [unoptimized + debuginfo] target(s) in 0.05s
$ cargo test -p flux-tests -- --test-args impl_trait
   Compiling flux-tests v0.1.0 (/path/to/flux/flux-tests)
    Finished test [unoptimized + debuginfo] target(s) in 0.62s
     Running tests/compiletest.rs (target/debug/deps/compiletest-1241128f1f51caa4)

running 5 tests
test [ui] pos/surface/impl_trait04.rs ... ok
test [ui] pos/surface/impl_trait03.rs ... ok
test [ui] pos/surface/impl_trait01.rs ... ok
test [ui] pos/surface/impl_trait00.rs ... ok
test [ui] pos/surface/impl_trait02.rs ... ok

test result: ok. 5 passed; 0 failed; 0 ignored; 0 measured; 191 filtered out; finished in 0.10s


running 2 tests
test [compile-fail] neg/surface/impl_trait00.rs ... ok
test [compile-fail] neg/surface/impl_trait02.rs ... ok

test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 207 filtered out; finished in 0.09s
```

## Testing Flux on a File

When working on Flux, you may want to test your changes by running it against a test file.
You can use `cargo xtask run <input>` to run Flux on a single input file.
The command will set appropriate flags to be able to use custom Flux attributes and macros,
plus some extra flags useful for debugging.
For example:

```console
$ cat test.rs
#[flux::sig(fn(x: i32) -> i32[x + 1])]
fn add1(x: i32) -> i32 {
    x + 1
}
$ cargo xtask run test.rs
```

The command will use a super set of the flags passed when running regression tests.
Thus, a common workflow is to identify a failing test and run it directly with `cargo xtask run`,
or alternatively copy it to a different file.

You may also find useful to create a directory in the root of the project and add it to
[`.git/info/exclude`](https://git-scm.com/docs/gitignore).
You can keep files there, outside of version control, and test Flux against them.
I have a directory called `attic/` where I keep a file named `playground.rs`.
To run Flux on it, I do `cargo xtask run attic/playground.rs`.

## Reporting locations where errors are emitted

When you use `cargo xtask run` you'll see that we report the location an error was emitted, e.g.,

```console
error[FLUX]: refinement type error
 --> attic/playground.rs:4:5
  |
4 |     0
  |     ^ a postcondition cannot be proved
-Ztrack-diagnostics: created at crates/flux-refineck/src/lib.rs:114:15   <------- this
```

You can also pass `-Ztrack-diagnostics=y` to enable it if you are not using `cargo xtask run`

## Running outside the project

To run Flux in a package outside the flux repo you need to install the binaries globally. You can
do that using `cargo xtask install`. If you are continuously testing new changes it could be annoying
to do it each time. To deal with this, you can set the `FLUX_SYSROOT` environment variable to change the
location where `cargo-flux` and `rustc-flux` load the `flux-driver`. You can set it globally to point
to the `target/debug` directory inside your local copy of the repo. This way you won't have to run
`cargo xtask install` after every change, and you can be sure you'll be using the latest local debug
build. Just be aware that the `rustc-flux` and `cargo-flux` binaries are built for a specific toolchain,
and you will get a dynamic linking error if the `flux-driver` was compiled with a different one. This
is to say, you should at least run `cargo xtask install` every time after the toolchain is updated.

## Profiling Flux

Set `FLUX_DUMP_TIMINGS=true` to have flux write timing diagnostics to `./log/timings`.

Right now this is _extremely_ simple, it just provides some details for the spans under `flux_typeck` and `flux_driver`.

### Sample output

Below is a sample output for an invocation of `cargo-flux check` that took 19 seconds. The missing 2 seconds approximately accounts for the time it takes for `cargo check` to run.

Note that `check_crate` contains everything running under `check_top`, which is why the sum of the spans is greater than 19 seconds.

```text
check_top
  Checker::infer
    num events:   205
    min non-zero: 0.52ms
    1st quartile: 0.52ms
    2nd quartile: 1.05ms
    3rd quartile: 2.62ms
    max:          24.12ms
    total time:   229.64ms
  Checker::check
    num events:   205
    min non-zero: 0.52ms
    1st quartile: 0.52ms
    2nd quartile: 1.05ms
    3rd quartile: 5.24ms
    max:          159.91ms
    total time:   2028.47ms
  FixpointCtx::check
    num events:   205
    min non-zero: 22.02ms
    1st quartile: 26.21ms
    2nd quartile: 28.31ms
    3rd quartile: 40.37ms
    max:          1867.51ms
    total time:   9106.36ms
total time: 11364.47ms

check_crate
  Callbacks::check_wf
    num events:   1
    min non-zero: 18.35ms
    1st quartile: 18.87ms
    2nd quartile: 18.87ms
    3rd quartile: 18.87ms
    max:          18.87ms
    total time:   18.87ms
  Callbacks::check_crate
    num events:   1
    min non-zero: 16986.93ms
    1st quartile: 16995.32ms
    2nd quartile: 16995.32ms
    3rd quartile: 16995.32ms
    max:          16995.32ms
    total time:   16995.32ms
total time: 17014.19ms
```
