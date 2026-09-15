//! Shared sysroot utilities for `flux-bin`, `xtask`, and `tests`.

use std::{
    collections::BTreeMap,
    env,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

/// Index of the sysroot, recording the name every artifact was given when it was copied in.
///
/// Written by `xtask`; read by `flux`, the test runner, and `flux-driver` to resolve the sysroot
/// crates by path instead of by name.
#[derive(Serialize, Deserialize, Default)]
pub struct SysrootManifest {
    #[serde(default)]
    pub crates: BTreeMap<String, SysrootCrate>,
}

/// File names are relative to the sysroot directory.
#[derive(Serialize, Deserialize, Default, Clone)]
pub struct SysrootCrate {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rlib: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rmeta: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fluxmeta: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dylib: Option<String>,
    /// Whether this crate's specs are injected as force externs under `-Fstd-extern-specs`.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub extern_spec: bool,
}

impl SysrootManifest {
    fn read(sysroot: &Path) -> Option<Self> {
        let content = std::fs::read_to_string(sysroot.join(SYSROOT_MANIFEST)).ok()?;
        toml::from_str(&content).ok()
    }

    /// Libraries get both their `.rmeta` and their `.rlib`: since cargo stopped embedding
    /// metadata in rlibs, the former is the only copy of the metadata and the latter is still
    /// needed to link.
    pub fn extern_args(sysroot: &Path) -> Vec<String> {
        let Some(manifest) = Self::read(sysroot) else { return vec![] };
        let mut args = vec![];
        for (name, krate) in &manifest.crates {
            for file in [&krate.rmeta, &krate.rlib, &krate.dylib]
                .into_iter()
                .flatten()
            {
                args.push("--extern".to_string());
                args.push(format!("{name}={}", sysroot.join(file).display()));
            }
        }
        args
    }

    pub fn extern_specs(sysroot: &Path) -> Vec<(String, PathBuf)> {
        let Some(manifest) = Self::read(sysroot) else { return vec![] };
        manifest
            .crates
            .iter()
            .filter(|(_, krate)| krate.extern_spec)
            .filter_map(|(name, krate)| Some((name.clone(), sysroot.join(krate.rmeta.as_ref()?))))
            .collect()
    }
}

pub const SYSROOT_MANIFEST: &str = "sysroot.toml";

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
