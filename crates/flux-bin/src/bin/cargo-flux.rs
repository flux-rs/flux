use std::{
    env,
    path::PathBuf,
    process::{Command, exit},
};

use anyhow::Result;
use flux_bin::utils::{
    EXIT_ERR, LIB_PATH, get_flux_driver_path, get_rust_toolchain, get_rustc_driver_lib_path,
    prepend_path_to_env_var,
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

    // Cargo can be called like `cargo [OPTIONS] flux`, so we skip all arguments until `flux` is
    // found.
    let args = env::args()
        .skip_while(|arg| arg != "flux")
        .skip(1)
        .collect::<Vec<_>>();

    let cargo_path = env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());
    let cargo_target = env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let cargo_target = PathBuf::from_iter([cargo_target, "flux".to_string()]);

    let mut cmd = Command::new(cargo_path);

    // Unless we are calling `cargo flux clean` append a check
    match &args[..] {
        [subcommand, ..] if subcommand == "clean" => {}
        _ => {
            cmd.arg("check");
        }
    }

    let exit_code = cmd
        .args(args)
        .env(LIB_PATH, extended_lib_path)
        .env("FLUX_BUILD_SYSROOT", "1")
        .env("FLUX_CARGO", "1")
        .env("RUST_TOOLCHAIN", rust_toolchain.clone())
        .env("RUSTUP_TOOLCHAIN", rust_toolchain)
        .env("RUSTC", flux_driver_path)
        .env("CARGO_TARGET_DIR", cargo_target)
        .status()?
        .code();

    Ok(exit_code.unwrap_or(EXIT_ERR))
}
