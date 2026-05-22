pub const FLUX_SYSROOT: &str = "FLUX_SYSROOT";

/// Rustc flags to pass Flux when running tests
pub fn default_flags() -> Vec<String> {
    vec!["--crate-type=rlib".to_string(), "--edition=2021".to_string()]
}
