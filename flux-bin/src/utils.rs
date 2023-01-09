use std::{env, error::Error, ffi::OsString, fs, path::PathBuf};

#[cfg(target_os = "windows")]
pub const LIB_PATH: &str = "PATH";
#[cfg(target_os = "linux")]
pub const LIB_PATH: &str = "LD_LIBRARY_PATH";
#[cfg(target_os = "macos")]
pub const LIB_PATH: &str = "DYLD_FALLBACK_LIBRARY_PATH";

pub const EXIT_ERR: i32 = -1;

// It's better than using .expect(), right?
pub fn report_err(message: &str, err: impl Error) -> i32 {
    println!("{}\nerror={}", message, err);
    EXIT_ERR
}

pub fn report_message(message: &str) -> i32 {
    println!("{}", message);
    EXIT_ERR
}

pub fn get_flux_path() -> Result<PathBuf, i32> {
    let mut flux_path = env::current_exe()
        .map_err(|e| report_err("Could not find the current execution's path", e))
        .map(|path| path.with_file_name("flux"))?;
    if cfg!(target_os = "windows") {
        flux_path.set_extension("exe");
    }

    if !flux_path.is_file() {
        return Err(report_message(&format!(
            "flux executable {:?} does not exist or is not a file",
            flux_path
        )));
    }
    Ok(flux_path)
}

pub fn get_rust_toolchain() -> Result<String, i32> {
    let toolchain_str = include_str!("../../rust-toolchain");
    let toolchain_file = rust_toolchain_file::toml::Parser::new(toolchain_str)
        .parse()
        .map_err(|e| report_err("Could not parse rust-toolchain file", e))?;
    toolchain_file
        .toolchain()
        .spec()
        .ok_or_else(|| report_message("No spec in rust-toolchain file"))?
        .channel()
        .ok_or_else(|| report_message("No channel in rust-toolchain file"))
        .map(|channel| channel.name().to_string())
}

pub fn get_dyld_fallback_library_path(rust_toolchain: &str) -> Result<PathBuf, i32> {
    let rustup_home_path = get_rustup_home()?;
    let toolchains_path = rustup_home_path.join("toolchains");
    if toolchains_path.is_dir() {
        let entries = fs::read_dir(toolchains_path.clone())
            .map_err(|e| report_err("Could not read Rustup toolchains folder", e))?;
        for entry in entries {
            let toolchain_entry =
                entry.map_err(|e| report_err("Could not read Rustup toolchains contents", e))?;
            let file_name = toolchain_entry.file_name().into_string().map_err(|name| {
                report_message(&format!("Could not convert Rustup toolchain file name: {:?}", name))
            })?;
            if file_name.starts_with(rust_toolchain) {
                return toolchain_entry
                    .path()
                    .join("lib")
                    .canonicalize()
                    .map_err(|e| report_err("Could not canonicalize rustup toolchain path", e));
            }
        }
    }
    Err(report_message("Could not read Rustup toolchains folder"))
}

pub fn get_rustup_home() -> Result<PathBuf, i32> {
    env::var("RUSTUP_HOME")
        .map(|home_dir| PathBuf::from(&home_dir))
        .or_else(|e| {
            match e {
                env::VarError::NotPresent => {
                    dirs::home_dir()
                        .ok_or_else(|| report_message("Could not get OS's home dir"))
                        .map(|home_dir| home_dir.join(".rustup"))
                }
                _ => Err(report_err("Could not read env var RUSTUP_HOME", e)),
            }
        })
}

/// Prepends the path so that it's the first checked.
pub fn extend_env_var_with_path(var_name: &str, new_path: PathBuf) -> Result<OsString, i32> {
    let mut paths = env::var(var_name)
        .map(|paths_str| env::split_paths(&paths_str).collect::<Vec<_>>())
        .or_else(|err| {
            match err {
                env::VarError::NotPresent => Ok(Vec::new()),
                _ => Err(report_err(&format!("Could not read env var {}", var_name), err)),
            }
        })?;
    // clone the path so we can report it in the error message.
    paths.insert(0, new_path.clone());
    env::join_paths(paths.into_iter()).map_err(|e| {
        report_err(&format!("Error prepending path {:?} to env var {}", new_path, var_name), e)
    })
}
