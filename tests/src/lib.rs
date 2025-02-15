pub const FLUX_SYSROOT: &str = "FLUX_SYSROOT";
pub const FLUX_FULL_COMPILATION: &str = "FLUX_FULL_COMPILATION";
pub const FLUX_SYSROOT_TEST: &str = "FLUX_SYSROOT_TEST";

/// Rustc flags to pass Flux when running tests
pub fn default_rustc_flags() -> Vec<String> {
    vec!["--crate-type=rlib".to_string(), "--edition=2021".to_string()]
}
