# Z3 Suggestion Backend Reproductions

These commands assume:

- Flux is checked out at `/home/cole/research/flux`.
- Benchmarks are checked out at `/home/cole/research/flux-wick-benchmarks`.
- The benchmark workspace dependencies in `Cargo.toml` point to
  `../flux/lib/flux-rs`, `../flux/lib/flux-core`, and
  `../flux/lib/flux-alloc`.
- The local sysroot was built with `cargo x --suggestions build-sysroot`.

Set the local compiler for benchmark commands:

```sh
export FLUX_SYSROOT=/home/cole/research/flux/sysroot
```

## Current Wave Weak-KVar Decode Panic

Reproduce with:

```sh
cd /home/cole/research/flux-wick-benchmarks
timeout 300s cargo flux -p wave
```

After emitting 41 refinement errors and 35 suggestions, Flux currently panics
at `crates/flux-infer/src/fixpoint_encoding/decoding.rs:220`:

```text
internal error: entered unreachable code: Weak kvar ids should be converted as part of fixpoint::Expr::WKVar
```

This occurs with both the one-shot and reused-process suggestion backends. It is
after the suggestion work used for the timing comparison and is not caused by
the persistent Z3 protocol.

## Fixed Suggestion Fallback Panic

Before commit `b06b6f4a76`, Wave panicked earlier at
`crates/flux-infer/src/suggestions.rs` while falling back to the original head:

```text
called `Result::unwrap()` on an `Err` value: NoGlobalVar(0)
```

Reproduce the old behavior from commit `1afb9c92af`:

```sh
git checkout 1afb9c92af
cargo x --suggestions build-sysroot
cd ../flux-wick-benchmarks
FLUX_SYSROOT=../flux/sysroot timeout 300s cargo flux -p wave
```

The fix treats failure to convert the fallback expression as a best-effort
suggestion failure instead of crashing.

## Binding Backend Wave UIF Panic

The pre-migration Rust binding backend cannot complete a full Wave comparison.
It panics in `lib/liquid-fixpoint/src/cstr2smt2.rs` while encoding the
uninterpreted function `flag_set`:

```text
error if function not present Global(... name: "flag_set")
```

Reproduce from the pre-migration commit after enabling the existing suggestion
feature through `flux-driver`:

```sh
git checkout 1be569a1fb
cargo x --suggestions build-sysroot
cd ../flux-wick-benchmarks
FLUX_SYSROOT=../flux/sysroot timeout 300s cargo flux -p wave
```

Because bindings stop before Wave emits its normal diagnostic set, there is no
valid full-Wave bindings timing. Focused functions that avoid this UIF are
comparable:

```sh
cargo flux -p wave --only-check='def:path_resolution::expand_path'
cargo flux -p wave --only-check='def:runtime::read_u32_pair'
```

Observed warm timings were 0.89 s bindings versus 0.91 s reused process for
`expand_path`, and 1.28 s bindings versus 0.88 s reused process for
`read_u32_pair`.

## Stale PLDI23 Benchmark Specs

The full `pldi23` crate currently fails before checking `dotprod` because its
old `Vec<T, A>` extern spec declares `push` and `len` in the same extern impl:

```text
invalid impl extern spec
items in this extern spec are not defined in the same extern impl block
```

After temporarily splitting `push` and `len` into separate `#[extern_spec]`
impls, unrelated `simplex` declarations also fail to resolve `Rmat`. For the
focused polymorphic trial, temporarily expose only `dotprod` and `vec` from
`benchmarks/pldi23/src/lib.rs`, then run:

```sh
cargo flux -p pldi23 --only-check='def:dotprod::dotprod'
```

The subprocess backend produces:

```text
requires v2.len >= v1.len
```

The benchmark-only isolation edits were not retained.

## Initial Persistent-Session Deadlock

The first persistent-session implementation held the stderr buffer mutex while
blocking in `read_to_end`, then attempted to acquire the same mutex after every
stdout response. A bounded focused run exposed the deadlock:

```sh
timeout 60s cargo flux -p flux-demo --only-check='def:neural::dot_product'
```

The fix reads stderr in chunks and holds the mutex only while appending each
chunk. The same command now completes normally.

## Benchmark Dependency Version Mismatch

Using the benchmark repository's original Git dependencies with a driver from
this checkout can panic because Flux metadata and the compiler revision do not
match. The observed panic was:

```text
def id points to dummy local item
```

Use local path dependencies in the benchmark workspace when testing a local
compiler checkout. This is benchmark setup, not a suggestion-backend failure.

## Timing Summary

All times are warm wall-clock measurements and include the surrounding focused
or full Cargo/Flux invocation.

| Workload | Bindings | One-shot process | Reused process |
| --- | ---: | ---: | ---: |
| `flux-demo`, full | 1.76 s | 5.95 s | 2.07 s |
| Wave, full to weak-KVar panic | unavailable | 6.53 s | 2.45 s |
| Wave `expand_path` | 0.89 s | not measured | 0.91 s |
| Wave `read_u32_pair` | 1.28 s | not measured | 0.88 s |

The full Wave one-shot and reused runs emitted the same 41 errors and 35
suggestions before the shared weak-KVar decode panic.
