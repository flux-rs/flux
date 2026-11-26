//! Shared sysroot utilities for `flux-bin`, `flux-driver`, `xtask`, and `tests`.

pub mod dev;
pub mod install;

use std::{
    collections::BTreeMap,
    env, fmt, fs,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

/// Index of the sysroot, recording the name every artifact was given when it was copied in.
///
/// Written by `xtask`; read by `flux`, the test runner, and `flux-driver` to resolve the sysroot
/// crates by path instead of by name.
#[derive(Serialize, Deserialize)]
pub struct SysrootManifest {
    /// Rust toolchain `flux-driver` was built with, and therefore must run with, e.g.,
    /// `nightly-2026-11-21-x86_64-unknown-linux-gnu`.
    pub toolchain: String,
    /// Version of Flux the sysroot was built from.
    pub version: FluxVersion,
    #[serde(default)]
    pub crates: BTreeMap<String, SysrootCrate>,
}

/// Where users are pointed to when their installation is broken.
pub const INSTALL_GUIDE_URL: &str = "https://flux-rs.github.io/flux/guide/install.html";

/// Error returned when the sysroot's manifest is missing or malformed. The error message suggests
/// reinstalling Flux.
#[derive(Debug)]
pub struct InvalidSysroot {
    sysroot: PathBuf,
    reason: String,
}

impl fmt::Display for InvalidSysroot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "invalid Flux sysroot at `{}`", self.sysroot.display())?;
        writeln!(f, "note: {}", self.reason)?;
        write!(f, "help: try reinstalling Flux (see {INSTALL_GUIDE_URL})")
    }
}

impl std::error::Error for InvalidSysroot {}

#[derive(Deserialize)]
struct ToolchainFile {
    toolchain: ToolchainSpec,
}

#[derive(Deserialize)]
struct ToolchainSpec {
    channel: String,
}

/// Returns the channel of a toolchain given the contents of its `rust-toolchain.toml` file.
pub fn parse_toolchain_file(content: &str) -> Result<String, toml::de::Error> {
    let file: ToolchainFile = toml::from_str(content)?;
    Ok(file.toolchain.channel)
}

/// Git version of the Flux sources a sysroot was built from, recorded when the sysroot is built.
#[derive(Serialize, Deserialize, Clone)]
pub struct FluxVersion {
    /// Abbreviated commit hash
    pub sha: String,
    /// Full commit hash
    pub sha_full: String,
    /// Commit date, formatted as `YYYY-MM-DD`
    pub date: String,
}

/// File names are relative to the sysroot's `lib` directory.
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
    /// Reads the manifest of `sysroot`.
    pub fn read(sysroot: &Path) -> Result<Self, InvalidSysroot> {
        let path = sysroot.join(SYSROOT_MANIFEST);
        let invalid = |reason| InvalidSysroot { sysroot: sysroot.to_path_buf(), reason };
        let content = fs::read_to_string(&path)
            .map_err(|err| invalid(format!("failed to read `{}`: {err}", path.display())))?;
        toml::from_str(&content).map_err(|err| {
            invalid(format!("failed to parse `{}`: {}", path.display(), err.message()))
        })
    }

    /// Libraries get both their `.rmeta` and their `.rlib`: since cargo stopped embedding
    /// metadata in rlibs, the former is the only copy of the metadata and the latter is still
    /// needed to link.
    pub fn extern_args(sysroot: &Path) -> Vec<String> {
        let Ok(manifest) = Self::read(sysroot) else { return vec![] };
        let mut args = vec![];
        for (name, krate) in &manifest.crates {
            for file in [&krate.rmeta, &krate.rlib, &krate.dylib]
                .into_iter()
                .flatten()
            {
                args.push("--extern".to_string());
                args.push(format!("{name}={}", lib_dir(sysroot).join(file).display()));
            }
        }
        args
    }

    pub fn extern_specs(sysroot: &Path) -> Vec<(String, PathBuf)> {
        let Ok(manifest) = Self::read(sysroot) else { return vec![] };
        manifest
            .crates
            .iter()
            .filter(|(_, krate)| krate.extern_spec)
            .filter_map(|(name, krate)| {
                Some((name.clone(), lib_dir(sysroot).join(krate.rmeta.as_ref()?)))
            })
            .collect()
    }
}

/// The sysroot is a self-contained directory with the following layout:
///
/// ```text
/// sysroot.toml                     the manifest, see [`SysrootManifest`]
/// bin/{cargo-flux,flux,flux-driver}
/// lib/                             precompiled Flux libraries
/// ```
pub const SYSROOT_MANIFEST: &str = "sysroot.toml";

/// Returns the directory of the sysroot holding the binaries.
pub fn bin_dir(sysroot: &Path) -> PathBuf {
    sysroot.join("bin")
}

/// Returns the directory of the sysroot holding the precompiled libraries.
pub fn lib_dir(sysroot: &Path) -> PathBuf {
    sysroot.join("lib")
}

/// Returns the path of the binary `name` in the sysroot.
pub fn bin_path(sysroot: &Path, name: &str) -> PathBuf {
    bin_dir(sysroot).join(format!("{name}{}", env::consts::EXE_SUFFIX))
}

/// Name of the environment variable used to override the Flux sysroot location.
///
/// When unset, the default is `$FLUX_HOME/sysroot` (managed by `cargo x install`). Set this variable
/// to redirect `flux` and `cargo-flux` to a different sysroot.
///
/// During development, `cargo x build-sysroot` populates `<workspace-root>/sysroot/`. The test
/// runner (`cargo x test`) automatically sets `FLUX_SYSROOT` to that directory so tests use the
/// locally built artifacts instead of the installed ones.
pub const FLUX_SYSROOT: &str = "FLUX_SYSROOT";

/// Returns the path to the active Flux sysroot, i.e., [`FLUX_SYSROOT`] or `$FLUX_HOME/sysroot` if
/// not set.
pub fn flux_sysroot_dir() -> PathBuf {
    env::var_os(FLUX_SYSROOT).map_or_else(default_flux_sysroot_dir, PathBuf::from)
}

/// Environment variable overriding the Flux home directory.
///
/// Like `CARGO_HOME` for cargo, the Flux home holds the user-level configuration file
/// (`config.toml`) and the default installation of the sysroot (`sysroot/`). When unset, the
/// default is `~/.flux`.
pub const FLUX_HOME: &str = "FLUX_HOME";

/// Returns the Flux home directory, i.e., [`FLUX_HOME`] or `~/.flux` if not set.
pub fn flux_home_dir() -> PathBuf {
    env::var_os(FLUX_HOME).map_or_else(
        || {
            home::home_dir()
                .expect("Couldn't find home directory")
                .join(".flux")
        },
        PathBuf::from,
    )
}

/// Returns `$FLUX_HOME/sysroot`, the default Flux sysroot when [`FLUX_SYSROOT`] is not set.
pub fn default_flux_sysroot_dir() -> PathBuf {
    flux_home_dir().join("sysroot")
}
