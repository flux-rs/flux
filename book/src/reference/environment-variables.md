# Environment Variables

Flux reads and sets a number of environment variables. Here is a list of them, organized by when
Flux interacts with them.

## Environment variables Flux reads

- `FLUXFLAGS` — Space-separated flags passed by `cargo flux` to every package checked by Flux,
  e.g., `FLUXFLAGS="-Ftimings" cargo flux`. Replaces
  [`build.fluxflags`](config.md#buildfluxflags). See
  [how flags are combined](config.md#how-flags-are-combined).
- `FLUX_ENCODED_FLAGS` — Like `FLUXFLAGS`, but flags are separated by the `0x1f` character (ASCII
  Unit Separator), which allows flags containing spaces. Takes precedence over `FLUXFLAGS`, like
  cargo's `CARGO_ENCODED_RUSTFLAGS`.
- `FLUX_HOME` — The Flux home directory, which holds the user configuration
  (`$FLUX_HOME/config.toml`) and the default sysroot. Defaults to `$HOME/.flux`. See
  [Flux Home](../guide/install.md#flux-home).
- `FLUX_SYSROOT` — The sysroot used by `flux` and `cargo flux`, i.e., the directory containing
  `flux-driver` and the precompiled Flux libraries. Defaults to `$FLUX_HOME/sysroot`.
- `FLUX_DRIVER` — Path to the `flux-driver` binary. Defaults to `$FLUX_SYSROOT/flux-driver`.

## Environment variables `cargo flux` sets

`cargo flux` runs cargo with the following variables:

- `RUSTC` — Set to the path of `flux-driver`, so that cargo runs Flux instead of `rustc`. It is set
  even if `RUSTC` is already set.
- `RUSTC_WRAPPER` — Set to an empty value to avoid conflicts with other wrappers.

`FLUX_CARGO` and `FLUX_BUILD_SYSROOT` are also set. They are used internally by the driver and
should not be set manually.
