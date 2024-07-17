use std::{env, ffi::OsString, fs, path::PathBuf};

use anyhow::{anyhow, Result};
use serde::Deserialize;

#[cfg(target_os = "windows")]
pub const LIB_PATH: &str = "PATH";
#[cfg(any(target_os = "linux", target_os = "freebsd"))]
pub const LIB_PATH: &str = "LD_LIBRARY_PATH";
#[cfg(target_os = "macos")]
pub const LIB_PATH: &str = "DYLD_FALLBACK_LIBRARY_PATH";

pub const EXIT_ERR: i32 = -1;

// CODESYNC(sysroot-env) we must use the same env var in flux-tests
pub const FLUX_SYSROOT: &str = "FLUX_SYSROOT";

/// The path of the flux sysroot lib containing precompiled libraries and the flux driver.
pub fn sysroot_dir() -> PathBuf {
    env::var(FLUX_SYSROOT).map_or_else(|_| default_sysroot_dir(), PathBuf::from)
}

#[derive(Deserialize)]
pub struct ToolchainToml {
    toolchain: ToolchainSpec,
}

#[derive(Deserialize)]
pub struct ToolchainSpec {
    channel: String,
}

/// Return the default sysroot
// CODESYNC(default-sysroot) we must use the same dir used in xtask
fn default_sysroot_dir() -> PathBuf {
    home::home_dir()
        .expect("Couldn't find home directory")
        .join(".flux")
}

pub fn get_flux_driver_path() -> Result<PathBuf> {
    let mut path = sysroot_dir().join("flux-driver");
    if cfg!(target_os = "windows") {
        path.set_extension("exe");
    }
    if !path.is_file() {
        return Err(anyhow!("flux executable {:?} does not exist or is not a file", path));
    }
    Ok(path)
}

pub fn get_rust_toolchain() -> Result<String> {
    let toolchain_str = include_str!("../../../rust-toolchain");
    let toolchain_file: ToolchainToml = toml::from_str(toolchain_str)?;
    Ok(toolchain_file.toolchain.channel)
}

/// Path from where to load the rustc-driver library from
pub fn get_rustc_driver_lib_path(rust_toolchain: &str) -> Result<PathBuf> {
    let toolchains_path = home::rustup_home()?.join("toolchains");
    if toolchains_path.is_dir() {
        let entries = fs::read_dir(toolchains_path)?;
        for entry in entries {
            let toolchain_entry = entry?;
            let file_name = toolchain_entry.file_name().into_string().map_err(|name| {
                anyhow!("Could not convert Rustup toolchain file name: {:?}", name)
            })?;
            if file_name.starts_with(rust_toolchain) {
                return toolchain_entry
                    .path()
                    .join("lib")
                    .canonicalize()
                    .map_err(anyhow::Error::from);
            }
        }
    }
    Err(anyhow!("Could not read Rustup toolchains folder"))
}

/// Prepends the path so that it's the first checked.
pub fn prepend_path_to_env_var(var_name: &str, new_path: PathBuf) -> Result<OsString> {
    let mut paths = match env::var(var_name) {
        Ok(paths) => env::split_paths(&paths).collect(),
        Err(env::VarError::NotPresent) => vec![],
        Err(e) => Err(e)?,
    };
    paths.insert(0, new_path);
    env::join_paths(paths).map_err(anyhow::Error::from)
}
