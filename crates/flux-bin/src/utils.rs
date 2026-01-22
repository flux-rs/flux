use std::{
    env,
    ffi::OsString,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Result, anyhow};
use serde::Deserialize;

#[cfg(target_os = "windows")]
pub const LIB_PATH: &str = "PATH";
#[cfg(any(target_os = "linux", target_os = "freebsd"))]
pub const LIB_PATH: &str = "LD_LIBRARY_PATH";
#[cfg(target_os = "macos")]
pub const LIB_PATH: &str = "DYLD_FALLBACK_LIBRARY_PATH";

pub const EXIT_ERR: i32 = -1;

pub const FLUX_SYSROOT: &str = "FLUX_SYSROOT";

const FLUX_DRIVER: &str = "FLUX_DRIVER";

/// The path of the flux sysroot lib containing precompiled libraries and the flux driver.
pub fn flux_sysroot_dir() -> PathBuf {
    env::var_os(FLUX_SYSROOT).map_or_else(default_flux_sysroot_dir, PathBuf::from)
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
fn default_flux_sysroot_dir() -> PathBuf {
    home::home_dir()
        .expect("Couldn't find home directory")
        .join(".flux")
}

pub fn get_flux_driver_path(sysroot: &Path) -> Result<PathBuf> {
    let path = if let Some(path) = env::var_os(FLUX_DRIVER) {
        PathBuf::from(path)
    } else {
        let mut path = sysroot.join("flux-driver");
        if cfg!(target_os = "windows") {
            path.set_extension("exe");
        }
        path
    };
    if !path.is_file() {
        return Err(anyhow!("path to flux-driver {:?} does not exist or is not a file", path));
    }
    Ok(path)
}

pub fn get_rust_toolchain() -> Result<String> {
    let toolchain_str = include_str!("../../../rust-toolchain.toml");
    let toolchain_file: ToolchainToml = toml::from_str(toolchain_str)?;
    Ok(toolchain_file.toolchain.channel)
}

pub fn get_binary_path(toolchain: &str, bin: &str) -> anyhow::Result<PathBuf> {
    let output = Command::new("rustup")
        .args(["which", "--toolchain", toolchain, bin])
        .output()
        .map_err(|e| anyhow!("failed to run `rustup which`: {e}"))?;

    if !output.status.success() {
        return Err(anyhow!("`rustup which` failed: {}", String::from_utf8_lossy(&output.stderr)));
    }

    Ok(PathBuf::from(
        String::from_utf8(output.stdout)
            .map_err(|e| anyhow!("invalid utf8 from `rustup which` output: {e}"))?
            .trim()
            .to_string(),
    ))
}

pub fn get_rust_sysroot(toolchain: &str) -> Result<PathBuf> {
    let out = Command::new("rustc")
        .arg(format!("+{toolchain}"))
        .args(["--print", "sysroot"])
        .output()?;
    bytes_to_pathbuf(out.stdout)
}

/// Path from where to load the rustc-driver library from
pub fn get_rust_lib_path(sysroot: &Path) -> PathBuf {
    if cfg!(windows) { sysroot.join("bin") } else { sysroot.join("lib") }
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

fn bytes_to_pathbuf(input: Vec<u8>) -> Result<PathBuf> {
    Ok(PathBuf::from(String::from_utf8(input)?.trim()))
}

pub fn get_version() -> &'static str {
    concat!(env!("GIT_SHA"), " (", env!("GIT_DATE"), ")")
}

pub fn get_version_full() -> &'static str {
    concat!(env!("GIT_SHA_FULL"), " (", env!("GIT_DATE"), ")")
}
