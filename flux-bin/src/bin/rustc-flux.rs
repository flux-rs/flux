use std::{
    env,
    process::{exit, Command},
};

use anyhow::Result;
use flux_bin::utils::{
    extend_env_var_with_path, get_ld_library_path, get_rust_toolchain, EXIT_ERR, LIB_PATH, get_flux_path,
};

fn main() {
    let exit_code = match run() {
        Ok(code) => code,
        Err(e) => {
            println!("Failed to run rustc-flux, error={}", e);
            EXIT_ERR
        }
    };
    exit(exit_code)
}

fn run() -> Result<i32> {
    let flux_path = get_flux_path()?;
    let rust_toolchain = get_rust_toolchain()?;
    let ld_library_path = get_ld_library_path(&rust_toolchain)?;
    let extended_lib_path = extend_env_var_with_path(LIB_PATH, ld_library_path)?;

    let exit_code = Command::new(flux_path)
        // Skip the invocation of rustc-flux itself
        .args(env::args().skip(1))
        .env(LIB_PATH, extended_lib_path)
        .env("RUST_TOOLCHAIN", rust_toolchain)
        .status()?
        .code();

    Ok(exit_code.unwrap_or(EXIT_ERR))
}
