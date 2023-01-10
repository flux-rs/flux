use std::{
    env,
    process::{exit, Command},
};

use flux_bin::utils::{
    extend_env_var_with_path, get_flux_path, get_ld_library_path, get_rust_toolchain, report_err,
    EXIT_ERR, LIB_PATH,
};

fn main() {
    if let Err(code) = run() {
        exit(code)
    }
}

fn run() -> Result<(), i32> {
    let flux_path = get_flux_path()?;
    let rust_toolchain = get_rust_toolchain()?;
    let ld_library_path = get_ld_library_path(&rust_toolchain)?;
    let extended_lib_path = extend_env_var_with_path(LIB_PATH, ld_library_path)?;

    let exit_status = Command::new("cargo")
        // Skip the invocation of cargo-flux itself
        .args(env::args().skip(1))
        .env(LIB_PATH, extended_lib_path)
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
