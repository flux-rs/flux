# The Manifest Format

Flux is configured for a package in the `[package.metadata.flux]` table of its `Cargo.toml`.
Cargo itself ignores this table. `cargo flux` reads it for every package in the dependency graph,
so a verified dependency is checked with the settings of its own manifest.

The table describes properties of the crate: _what_ is verified and under which semantics.
Settings that control _how_ `cargo flux` runs, e.g., caching or timeouts, live in
[`.flux/config.toml`](config.md) instead. The two never share a key.

```toml
[package.metadata.flux]
enabled = true
include = ["src/verified/**"]
check-overflow = "strict"
no-panic = true
allow-uninterpreted-cast = false
allow-raw-deref = "none"
lean = "off"
solver = "cvc5"
scrape-quals = true
uif-ops = "*,/"

[package.metadata.flux.trusted]
default = false
files = ["src/ffi/**"]

[package.metadata.flux.trusted-impl]
files = ["src/impls/**"]

[package.metadata.flux.ignore]
default = false
```

The keys of the table are described below. Keys use kebab-case. Unknown keys are an error.

## `enabled`

- Type: boolean
- Default: `false`

Flux only checks a package if `enabled` is `true`. Other packages are compiled as usual.

## `include`

- Type: array of [patterns](#patterns)
- Default: all files
- Flag: `-Finclude`

If present, only items in files matching one of the patterns are checked. The `--only-check`
option of `cargo flux` replaces these patterns for the packages it targets. See also
[Include Patterns](../guide/specifications.md#include-patterns).

## `check-overflow`

- Type: string (`none`, `lazy`, `strict-under` or `strict`)
- Default: `none`
- Flag: `-Fcheck-overflow`

How arithmetic overflow and underflow are checked. See
[Checking Overflows](../guide/specifications.md#checking-overflows).

## `no-panic`

- Type: boolean
- Default: `false`
- Flag: `-Fno-panic`

If `true`, every function is implicitly labeled with `no_panic`, so the only way a function can
panic is by calling an external function without this attribute.

## `allow-uninterpreted-cast`

- Type: boolean
- Default: `false`
- Flag: `-Fallow-uninterpreted-cast`

Allow uninterpreted casts between sorts. See
[Casting Sorts](../guide/specifications.md#casting-sorts).

## `allow-raw-deref`

- Type: string (`none` or `ok`)
- Default: `none`
- Flag: `-Fallow-raw-deref`

Whether raw pointer dereferences are allowed during refinement checking.

## `lean`

- Type: string (`off`, `emit` or `check`)
- Default: `off`
- Flag: `-Flean`

With `emit`, Flux emits Lean definitions and verification conditions for items proven externally.
With `check`, it also checks them.

## `solver`

- Type: string (`z3` or `cvc5`)
- Default: `z3`
- Flag: `-Fsolver`

The SMT solver used to verify the crate.

## `scrape-quals`

- Type: boolean
- Default: `false`
- Flag: `-Fscrape-quals`

Let fixpoint scrape qualifiers from the constraints. See
[Scraping Qualifiers](../guide/specifications.md#scraping-qualifiers).

## `uif-ops`

- Type: string (a comma separated list of operators)
- Default: none
- Flag: `-Fuif-ops`

Binary operators encoded as uninterpreted functions in the constraints. See
[Uninterpreted Operators](../guide/specifications.md#uninterpreted-operators).

## The `trusted` table

```toml
[package.metadata.flux.trusted]
default = false
files = ["src/ffi/**"]
```

- `default` (boolean, default `false`, flag `-Ftrusted`): if `true`, all code is trusted by default.
  Items can be untrusted with `#[trusted(no)]`.
- `files` (array of [patterns](#patterns), flag `-Finclude-trusted`): only consider items in files
  matching one of the patterns as trusted.

See [Ignored and trusted code](../guide/specifications.md#ignored-and-trusted-code).

## The `trusted-impl` table

```toml
[package.metadata.flux.trusted-impl]
files = ["src/impls/**"]
```

- `files` (array of [patterns](#patterns), flag `-Finclude-trusted-impl`): only consider items in
  files matching one of the patterns as `trusted_impl`.

## The `ignore` table

```toml
[package.metadata.flux.ignore]
default = false
```

- `default` (boolean, default `false`, flag `-Fignore`): if `true`, all code is ignored by default.
  Items can be unignored with `#[ignore(no)]`.

## Patterns

`include`, `trusted.files` and `trusted-impl.files` take patterns of the following forms:

- `glob:<pattern>` or a bare `<pattern>`: match files by glob, e.g., `src/ascii/*.rs`.
- `def:<name>`: match items whose name contains `<name>`.
- `span:<file>:<line>:<col>`: match the item at a source location.

File paths are relative to the directory containing `Cargo.toml`.

## Overriding a property for a single run

Crate properties cannot be set in `.flux/config.toml`. To try a different setting without editing
the manifest, pass the corresponding flag, e.g.,

```console
FLUXFLAGS="-Fsolver=z3" cargo flux
```

See [how flags are combined](config.md#how-flags-are-combined).
