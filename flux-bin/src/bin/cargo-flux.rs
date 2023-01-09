use std::{
    env,
    error::Error,
    fs,
    path::PathBuf,
    process::{exit, Command},
};

const EXIT_ERR: i32 = -1;

// It's better than using .expect(), right?
fn report_err(message: &str, err: impl Error) -> i32 {
    println!("{}\nerror={}", message, err);
    EXIT_ERR
}

fn report_message(message: &str) -> i32 {
    println!("{}", message);
    EXIT_ERR
}

fn main() {
    if let Err(code) = run() {
        exit(code)
    }
}

fn run() -> Result<(), i32> {
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

    let rust_toolchain = get_rust_toolchain()?;
    let dyld_fallback_library_path = get_dyld_fallback_library_path(&rust_toolchain)?;

    let exit_status = Command::new("cargo")
        // Skip the invocation of cargo-flux itself
        .args(env::args().skip(1))
        .env("DYLD_FALLBACK_LIBRARY_PATH", dyld_fallback_library_path)
        .env("RUST_TOOLCHAIN", rust_toolchain)
        .env("RUSTC_WRAPPER", flux_path)
        .status()
        .map_err(|e| report_err("Failed to run cargo", e))?;

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(EXIT_ERR))
    }
}

fn get_rust_toolchain() -> Result<String, i32> {
    let toolchain_str = include_str!("../../../rust-toolchain");
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

fn get_dyld_fallback_library_path(rust_toolchain: &str) -> Result<String, i32> {
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
                    .map_err(|e| report_err("Could not canonicalize rustup toolchain path", e))
                    .and_then(|path| {
                        let path_str = path
                            .as_path()
                            .to_str()
                            .ok_or_else(|| report_message("Could not render rustup toolchain path (is its name valid unicode?)"))?;
                        Ok(path_str.to_string())
                    });
            }
        }
    }
    Err(report_message("Could not read Rustup toolchains folder"))
}

fn get_rustup_home() -> Result<PathBuf, i32> {
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
