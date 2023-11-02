use std::{
    env,
    path::PathBuf,
    process::{exit, Command},
};

use anyhow::Result;
use flux_bin::utils::{
    get_flux_driver_path, get_rust_toolchain, get_rustc_driver_lib_path, prepend_path_to_env_var,
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
    let ld_library_path = get_rustc_driver_lib_path(&rust_toolchain)?;
    let extended_lib_path = prepend_path_to_env_var(LIB_PATH, ld_library_path)?;

    let cargo_target = env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let cargo_target = PathBuf::from_iter([cargo_target, "flux".to_string()]);

    let exit_code = Command::new("cargo")
        // Skip the invocation of cargo-flux itself
        .args(env::args().skip(1))
        .env(LIB_PATH, extended_lib_path)
        // CODESYNC(build-sysroot, 5) When running flux within cargo we want to compile flux libraries
        // as the precompiled versions.
        .env("FLUX_BUILD_SYSROOT", "1")
        // CODESYNC(flux-cargo) Tell the flux-driver it's being called from cargo.
        .env("FLUX_CARGO", "1")
        .env("RUST_TOOLCHAIN", rust_toolchain.clone())
        .env("RUSTUP_TOOLCHAIN", rust_toolchain)
        .env("RUSTC", flux_driver_path)
        .env("CARGO_TARGET_DIR", cargo_target)
        .status()?
        .code();

    Ok(exit_code.unwrap_or(EXIT_ERR))
}
