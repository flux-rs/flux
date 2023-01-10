use std::{env, ffi::OsString, fs, path::PathBuf};

use anyhow::{anyhow, Result};

#[cfg(target_os = "windows")]
pub const LIB_PATH: &str = "PATH";
#[cfg(target_os = "linux")]
pub const LIB_PATH: &str = "LD_LIBRARY_PATH";
#[cfg(target_os = "macos")]
pub const LIB_PATH: &str = "DYLD_FALLBACK_LIBRARY_PATH";

pub const EXIT_ERR: i32 = -1;

pub fn get_default_flux_path() -> Result<PathBuf> {
    let mut default_flux_path = env::current_exe().map(|path| path.with_file_name("flux"))?;
    if cfg!(target_os = "windows") {
        default_flux_path.set_extension("exe");
    }
    Ok(default_flux_path)
}

pub fn get_flux_path() -> Result<PathBuf> {
    let flux_path = env::var("FLUX_PATH").map(PathBuf::from).or_else(|err| {
        match err {
            env::VarError::NotPresent => get_default_flux_path(),
            _ => Err(anyhow::Error::from(err)),
        }
    })?;
    if !flux_path.is_file() {
        return Err(anyhow!("flux executable {:?} does not exist or is not a file", flux_path));
    }
    Ok(flux_path)
}

pub fn get_rust_toolchain() -> Result<String> {
    let toolchain_str = include_str!("../../rust-toolchain");
    let toolchain_file = rust_toolchain_file::toml::Parser::new(toolchain_str).parse()?;
    toolchain_file
        .toolchain()
        .spec()
        .ok_or_else(|| anyhow!("No spec in rust-toolchain file"))?
        .channel()
        .ok_or_else(|| anyhow!("No channel in rust-toolchain file"))
        .map(|channel| channel.name().to_string())
}

pub fn get_ld_library_path(rust_toolchain: &str) -> Result<PathBuf> {
    let rustup_home_path = get_rustup_home()?;
    let toolchains_path = rustup_home_path.join("toolchains");
    if toolchains_path.is_dir() {
        let entries = fs::read_dir(toolchains_path.clone())?;
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

pub fn get_rustup_home() -> Result<PathBuf> {
    env::var("RUSTUP_HOME").map(PathBuf::from).or_else(|e| {
        match e {
            env::VarError::NotPresent => {
                dirs::home_dir()
                    .ok_or_else(|| anyhow!("Could not get OS's home dir"))
                    .map(|home_dir| home_dir.join(".rustup"))
            }
            _ => Err(anyhow::Error::from(e)),
        }
    })
}

/// Prepends the path so that it's the first checked.
pub fn extend_env_var_with_path(var_name: &str, new_path: PathBuf) -> Result<OsString> {
    let mut paths = env::var(var_name)
        .map(|paths_str| env::split_paths(&paths_str).collect())
        .or_else(|err| {
            match err {
                env::VarError::NotPresent => Ok(Vec::new()),
                e => Err(e),
            }
        })?;
    // clone the path so we can report it in the error message.
    paths.insert(0, new_path.clone());
    env::join_paths(paths.into_iter()).map_err(anyhow::Error::from)
}
