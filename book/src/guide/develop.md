# Developer's Guide

## Backtraces

You can use the usual `RUST_BACKTRACE=1` environment variable to enable backtraces.
With the regular `release` build (`cargo x install`) you get some backtraces, but
the `dev` build, which you can install as shown below, gives more information e.g.
the source-spans of various calls in the backtrace.

```sh
$ cargo x install --profile dev
```

## Regression Tests

Run with `cargo x test [filename substring]` from the repository root.

This will build the flux binary and then run it against the entire test suite.
You can optionally pass a _filter_ to only run tests containing some substring.
For example:

```console
$ cargo x test impl_trait
   Compiling xtask v0.1.0 (/path/to/flux/xtask)
    Finished dev [unoptimized + debuginfo] target(s) in 0.29s
     Running `target/debug/xtask test impl_trait`
$ cargo build
    Finished dev [unoptimized + debuginfo] target(s) in 0.05s
$ cargo test -p tests -- --test-args impl_trait
   Compiling fluxtests v0.1.0 (/path/to/flux/tests)
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

### Test Suites

The test suite is split into two tiers based on what the test requires at compile time.

All test paths below are relative to the repository's `tests/` directory.

- `tests/pos/`: positive tests (pass).
- `tests/neg/`: negative tests (we are testing the errors emitted using `//~ ERROR`).
- `tests/rustfix/`: tests for rustfix (currently this is only for applying suggestions).
- `tests/with_deps/`: same as the above, with `flux_rs` and library specs available.
- `tests/todo/`: TODO tests (excluded from testing).

**Basic tests** (`tests/pos/`, `tests/neg/`, and `tests/rustfix/`) only require `flux_attrs`, the procedural macro
crate that provides Flux's surface syntax. **Prefer writing tests here whenever possible.**
A test belongs in the basic suite if it only uses Flux attributes directly, that is, it uses
`flux_attrs::*` (or `#[flux::*]`) without importing `flux_rs`, `flux_core`, or `flux_alloc`.

**Dependency tests** (`tests/with_deps/pos/`, `tests/with_deps/neg/`, and `tests/with_deps/rustfix/`) require the full set of
precompiled Flux libraries (`flux_rs`, `flux_core`, `flux_alloc`). Only place a test here when it
genuinely needs one of those libraries, for example, when testing extern specs for
standard-library types or behaviour that relies on the `flux_rs` prelude.

Use `--suite basic` or `--suite with-deps` to scope to basic tests or dependency tests, respectively.

### Where to put a test

There are a lot of subfolders. Most of the time you will just match the test to a feature,
e.g. `arrays/`, `enums/`, `extern_specs/`, `fold_unfold/`, or `impl_trait/`.

Use `tests/neg/error_messages/` when the test is about the error message itself.

Use an existing phase subfolder (`resolver/`, `desugar/`, `wf/`, etc.) when appropriate.

`surface/` is a bit of a catch-all, but is meant for surface tests.

### Writing rustfix tests

These tests check how `cargo flux fix` applies changes.

Tests are written as:

- `test-name.rs`: The test file.

  To ensure that we apply the changes, add `//@run-rustfix`,
  `//@rustfix-only-machine-applicable`, and any `//@compile-flags:`.
- `test-name.fixed`: the exact result of applying the fixes.
- `test-name.stderr`: the expected diagnostics from the original input, before
  applying fixes (if omitted, treated as empty).
  
These tests require that Flux succeeds on the .fixed file.

In many tests, we only care about applying the suggestion,
so add `//@normalize-stderr-test: "(?s).*" -> ""` to skip diagnostic-text snapshots.
What this does is turn stderr into the empty string—if you do this, you can then
skip adding a `.stderr`.

Tests requiring `flux_rs` or extern specs live in `tests/with_deps/rustfix/` and use
the same conventions.

#### Generating expected output

You can generate the `.fixed` and `.stderr` files if your test is on behavior that
currently works using `--bless`, e.g. `cargo x test my-test --bless`.

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

## Macro expansion

For example if you have code like in `path/to/file.rs`

```rust
#[extern_spec]
#[flux::refined_by(elems: Set<T>)]
struct HashSet<T, S = RandomState>;
```

and you want to see what the `extern_spec` macro expands it out to, then run

```shell
cargo x run -- -Zunpretty=expanded path/to/file.rs
```

Or you can run the `xtask` command directly

```shell
cargo x expand path/to/file.rs
```

## Examining the MIR

You can use the `-Zdump-mir` flag to dump the MIR at various stages of compilation.
For example,

```
$ cargo x run path/to/test.rs -- -Zdump-mir=renumber
```

or

```
$ cargo x run path/to/test.rs -- -Zdump-mir=ghost
```

will stash the MIR for those relevant stages in the `mir_dump` directory.

You can then look at the `<fn-name>.ghost.mir` to see the MIR that Flux is checking.

## Reporting and dealing with bugs

As Flux is under active development, there are many aspects of Rust that Flux does not yet support, are
only partially implemented, or where the implementation may contain bugs. These issues typically manifest
as unreachable arms in a match statement (that turn out not to be unreachable) or preemtive assertions to
guard against code we don't yet support. To help identify the code that triggers these bugs, there are a few
recommended methods for reporting them:

- `QueryErr::bug`: Use this method to report a bug if the code already returns a `QueryResult`. This
  approach is preferred because we will correctly recover from the error.
- `span_bug!`: When you have a `Span` at hand, you can use this macro in place of `panic!` to report
  the span before panicking.
- `tracked_span_bug!`: This macro is similar to `span_bug!`, but it uses a span stored in a thread local
  variable (if one exists). To track a span in the thread local variable you can use `flux_common::bug::track_span`.
- `bug!`: For other cases where none of the above applies, you can use the `bug!` macro. This behaves
  mostly like `panic!` but with nicer formatting.

When running Flux in a new code base, consider setting the flag `FLUX_CATCH_BUGS=1`. If this flag is set,
Flux will try to catch and recover from panics emitted with one of the bug macros (using
`std::panic::catch_unwind`). Bugs are caught at item boundaries. This may leave Flux or rustc
in an inconsistent state, so there are no guarantees that Flux will behave correctly after recovering
from a panic. However, this may still be useful to gather as many errors as possible. Code can
be selectively ignored later.

## Dumping the Checker Trace

```
cargo x install --debug
FLUX_DUMP_CHECKER_TRACE=1 FLUX_CHECK_DEF=mickey cargo flux
python3  path/to/flux/tools/logreader.py
```

## Debugging Extern Specs

To see the expanded code of an `extern_spec` macro, you can do

```
cargo x expand path/to/file.rs
```

## (Re)building Libraries

When making changes to the libraries, including `flux-core` which has the
`extern_spec`ifications for the standard library, you can force a rebuild
of the libraries by running:

```sh
cargo x build-sysroot
```
