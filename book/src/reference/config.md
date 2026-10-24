# Configuration

This page explains how `cargo flux` is configured through `.flux/config.toml` files, which control
_how_ Flux runs, e.g., caching, timeouts or extra output. Properties of a crate, i.e., _what_ is
verified, belong in its [manifest](manifest.md).

The configuration system follows the rules cargo uses for
[`.cargo/config.toml`](https://doc.rust-lang.org/cargo/reference/config.html).

## Hierarchical structure

`cargo flux` looks for configuration files in the current directory and all parent directories. If,
for example, it is invoked in `/projects/foo/bar`, then the following files are probed for and
merged in this order:

- `/projects/foo/bar/.flux/config.toml`
- `/projects/foo/.flux/config.toml`
- `/projects/.flux/config.toml`
- `/.flux/config.toml`
- `$FLUX_HOME/config.toml`, which defaults to `$HOME/.flux/config.toml` (see
  [Flux Home](../guide/install.md#flux-home))

This lets you check in a configuration for a project and keep personal defaults in your home
directory. The home configuration is not read twice if it is also found among the parent
directories.

If a key is set in multiple files, the values are merged. Numbers, strings and booleans from files
closer to the current directory take precedence, with the home configuration having the lowest
priority. Tables are merged key by key. Arrays are joined together, with items from higher
precedence files placed later.

## Configuration format

Configuration files are written in TOML. The following is an overview of all settings, with
detailed descriptions below.

```toml
[build]
fluxflags = ["-Ftimings"]      # extra flags for every package checked by Flux

[cache]
enabled = true                 # enable fixpoint query caching
dir = "flux-cache"             # where cache files are saved

[fixpoint]
timeout = 30                   # timeout in seconds for each fixpoint query

[diagnostics]
verbose = false                # more detailed error messages
suggestions = true             # emit suggestions
rerun-hint = true              # attach a command to re-run each failing item

[stats]
summary = true                 # print a summary of the items checked
timings = false                # print the time taken to check each function
annots = false                 # compute statistics about annotations

[debug]
log-dir = "log"                # where debug data is dumped
dump-constraint = false        # dump the fixpoint constraints
dump-fhir = false              # dump the fhir of each item
dump-rty = false               # dump the rty of each item
dump-checker-trace = "info"    # dump the checker's trace at this level
catch-bugs = false             # keep running after internal errors

[package."*"]                  # overrides for packages that are not workspace members
stats.summary = false

[package.my-crate]             # overrides for `my-crate`
fixpoint.timeout = 120
fluxflags = ["-Fdump-constraint"]
```

Unknown keys are an error. This includes crate properties, e.g., `solver`, which can only be set in
the manifest.

## Config-relative paths

Relative paths in a configuration file are resolved against the parent of the directory containing
the file. For example, `cache.dir = "flux-cache"` in `/my/project/.flux/config.toml` resolves to
`/my/project/flux-cache`.

## Package overrides

Settings can be overridden for specific packages with `[package.<spec>]` tables, similar to cargo's
[profile overrides](https://doc.rust-lang.org/cargo/reference/profiles.html#overrides). `<spec>`
can be:

- a package name, e.g., `[package.my-crate]`;
- a name and a version, e.g., `[package."my-crate@0.1.0"]`;
- `"*"`, which matches all packages that are not members of the workspace, e.g., verified
  dependencies.

A package table can contain any of the settings above, except `[build]`, plus a
[`fluxflags`](#packagespecfluxflags) key. Settings are merged field by field, in the following
order of precedence:

1. the table matching the package by name or by name and version;
2. `[package."*"]`, if the package is not a workspace member;
3. the top-level settings.

A spec that matches no package is reported as a warning. A package matched by more than one table,
e.g., by both `my-crate` and `my-crate@0.1.0`, is an error.

## How flags are combined

`cargo flux` translates the manifest and the configuration into `-F` flags for each package. Flags
are passed in the following order, and later flags take precedence:

1. flags `cargo flux` always sets: `-Fverify=on`, `-Ffull-compilation=on` and `-Fsysroot`;
2. flags derived from [`[package.metadata.flux]`](manifest.md);
3. flags derived from the settings in `.flux/config.toml`, after applying package overrides;
4. [`fluxflags`](#packagespecfluxflags) from the matching `[package.<spec>]` table;
5. the global flags, taken from the first source that is set among the
   [`FLUX_ENCODED_FLAGS`](environment-variables.md) and
   [`FLUXFLAGS`](environment-variables.md) environment variables and
   [`build.fluxflags`](#buildfluxflags);
6. flags passed on the command line, e.g., `--only-check`.

Like cargo's `RUSTFLAGS`, the sources of global flags are mutually exclusive: setting `FLUXFLAGS`,
even to an empty string, ignores `build.fluxflags`.

As with `RUSTFLAGS`, flags in `fluxflags`, `FLUXFLAGS` or `FLUX_ENCODED_FLAGS` are passed as they
are and can override any earlier flag, including crate properties and the flags `cargo flux` sets
itself. Mistakes are reported by Flux when it checks each crate. For the full list of flags, see
<https://flux-rs.github.io/flux/doc/flux_config/flags/struct.Flags.html>.

## Configuration keys

This section documents all configuration keys. Keys with variable parts are written with angle
brackets, like `package.<spec>.fluxflags`.

### `[build]`

#### `build.fluxflags`

- Type: string or array of strings
- Default: none
- Environment: `FLUX_ENCODED_FLAGS` or `FLUXFLAGS`

Extra flags passed to every package checked by Flux. The value may be an array of strings or a
space-separated string. See [how flags are combined](#how-flags-are-combined).

### `[cache]`

#### `cache.enabled`

- Type: boolean
- Default: `false`
- Flag: `-Fcache`

Enables fixpoint query caching. Every crate saves its cache in its own file inside
[`cache.dir`](#cachedir).

#### `cache.dir`

- Type: string (path)
- Default: `<target-dir>/flux-cache`

The directory where cache files are saved.

### `[fixpoint]`

#### `fixpoint.timeout`

- Type: integer (seconds)
- Default: none
- Flag: `-Ffixpoint-timeout`

Timeout for each fixpoint query. If a query doesn't finish in time, fixpoint is killed and an error
is reported for the item being checked.

### `[diagnostics]`

#### `diagnostics.verbose`

- Type: boolean
- Default: `false`
- Flag: `-Fflux-verbose`

Produce more detailed error messages, e.g., condition spans for fold errors.

#### `diagnostics.suggestions`

- Type: boolean
- Default: `true`
- Flag: `-Fno-suggestions` (inverted)

Emit suggestions in diagnostics.

#### `diagnostics.rerun-hint`

- Type: boolean
- Default: `true`
- Flag: `-Frerun-hint`

Attach a note to each failing item with a command to re-run the check on just that item.

### `[stats]`

#### `stats.summary`

- Type: boolean
- Default: `true`
- Flag: `-Fsummary`

Print a summary of the number of functions checked, trusted, etc.

#### `stats.timings`

- Type: boolean
- Default: `false`
- Flag: `-Ftimings`

Print the time taken to analyze each function, and dump a file with the raw times.

#### `stats.annots`

- Type: boolean
- Default: `false`
- Flag: `-Fannots`

Compute statistics about the number and size of annotations, and dump them to
[`debug.log-dir`](#debuglog-dir).

### `[debug]`

#### `debug.log-dir`

- Type: string (path)
- Default: `log` in the directory where the driver runs
- Flag: `-Flog-dir`

The directory where debug data is dumped.

#### `debug.dump-constraint`

- Type: boolean
- Default: `false`
- Flag: `-Fdump-constraint`

Dump the fixpoint constraints generated for each function.

#### `debug.dump-fhir`

- Type: boolean
- Default: `false`
- Flag: `-Fdump-fhir`

Dump the `fhir` of each item.

#### `debug.dump-rty`

- Type: boolean
- Default: `false`
- Flag: `-Fdump-rty`

Dump the `rty` of each item.

#### `debug.dump-checker-trace`

- Type: string (`error`, `warn`, `info`, `debug` or `trace`)
- Default: none
- Flag: `-Fdump-checker-trace`

Dump the checker's trace at the given level.

#### `debug.catch-bugs`

- Type: boolean
- Default: `false`
- Flag: `-Fcatch-bugs`

Keep running Flux after internal errors to report as many errors as possible.

### `[package]`

#### `package.<spec>.<setting>`

Any of the settings above, except `[build]`, overridden for the packages matching `<spec>`.
Per-package flags go in [`package.<spec>.fluxflags`](#packagespecfluxflags) instead of
`build.fluxflags`. See [Package overrides](#package-overrides).

#### `package.<spec>.fluxflags`

- Type: string or array of strings
- Default: none

Extra flags passed to the packages matching `<spec>`. The flags of a table matching the package by
name replace the ones from `[package."*"]`.
