use std::{
    env,
    process::{exit, Command},
};

use flux_bin::utils::{
    extend_env_var_with_path, get_dyld_fallback_library_path, get_rust_toolchain, report_err,
    EXIT_ERR, LIB_PATH,
};

fn main() {
    if let Err(code) = run() {
        exit(code)
    }
}

fn run() -> Result<(), i32> {
    let rust_toolchain = get_rust_toolchain()?;
    let dyld_fallback_library_path = get_dyld_fallback_library_path(&rust_toolchain)?;
    let extended_lib_path = extend_env_var_with_path(LIB_PATH, dyld_fallback_library_path)?;

    let exit_status = Command::new("flux")
        // Skip the invocation of rustc-flux itself
        .args(env::args().skip(1))
        .env(LIB_PATH, extended_lib_path)
        .env("RUST_TOOLCHAIN", rust_toolchain)
        .status()
        .map_err(|e| report_err("Failed to run flux (is it installed?)", e))?;

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(EXIT_ERR))
    }
}
