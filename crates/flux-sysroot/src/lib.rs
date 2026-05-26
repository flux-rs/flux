//! Shared sysroot utilities for `flux-bin`, `xtask`, and `tests`.

use std::{env, path::PathBuf};

/// Name of the environment variable used to override the Flux sysroot location.
///
/// The sysroot is a directory containing `flux-driver` and precompiled Flux libraries. When unset,
/// the default is `~/.flux` (managed by `cargo x install`). Set this variable to redirect
/// `flux` and `cargo-flux` to a different location, e.g., a custom or non-default install path.
///
/// During development, `cargo x build-sysroot` populates `<workspace-root>/sysroot/`. The test
/// runner (`cargo x test`) automatically sets `FLUX_SYSROOT` to that directory so tests use the
/// locally built artifacts instead of `~/.flux`.
pub const FLUX_SYSROOT: &str = "FLUX_SYSROOT";

/// Returns the path to the active Flux sysroot.
///
/// Both `cargo-flux` and `flux` call this at startup:
/// - `cargo-flux` uses it to locate `flux-driver` and sets `RUSTC=<driver>` before invoking cargo.
/// - `flux` uses it to locate `flux-driver` and passes `-L <sysroot>` so rustc can find the
///   precompiled extern crates (`flux_rs`, `flux_attrs`).
pub fn flux_sysroot_dir() -> PathBuf {
    env::var_os(FLUX_SYSROOT).map_or_else(default_flux_sysroot_dir, PathBuf::from)
}

/// Returns `~/.flux`, the default Flux sysroot when [`FLUX_SYSROOT`] is not set.
pub fn default_flux_sysroot_dir() -> PathBuf {
    home::home_dir()
        .expect("Couldn't find home directory")
        .join(".flux")
}
