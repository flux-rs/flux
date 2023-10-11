use std::{
    env,
    path::PathBuf,
    process::{exit, Command},
};

use anyhow::Result;
use flux_bin::utils::{
    extend_env_var_with_path, get_flux_driver_path, get_ld_library_path, get_rust_toolchain,
    EXIT_ERR, LIB_PATH,
};

fn main() {
    let exit_code = match run() {
        Ok(code) => code,
        Err(e) => {
            println!("Failed to run cargo-flux, error={e}");
            EXIT_ERR
        }
    };
    exit(exit_code)
}

fn run() -> Result<i32> {
    let flux_driver_path = get_flux_driver_path()?;
    let rust_toolchain = get_rust_toolchain()?;
    let ld_library_path = get_ld_library_path(&rust_toolchain)?;
    let extended_lib_path = extend_env_var_with_path(LIB_PATH, ld_library_path)?;

    let cargo_target = env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let cargo_target = PathBuf::from_iter([cargo_target, "flux".to_string()]);

    let features = ["--features", "flux-rs/enabled"].iter();

    let exit_code = Command::new("cargo")
        // Skip the invocation of cargo-flux itself
        .args(env::args().skip(1))
        .args(features)
        .env(LIB_PATH, extended_lib_path)
        .env("RUST_TOOLCHAIN", rust_toolchain.clone())
        .env("RUSTUP_TOOLCHAIN", rust_toolchain)
        .env("RUSTC", flux_driver_path)
        .env("CARGO_TARGET_DIR", cargo_target)
        .status()?
        .code();

    Ok(exit_code.unwrap_or(EXIT_ERR))
}
