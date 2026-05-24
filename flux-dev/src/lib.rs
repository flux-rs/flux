//! Shared development utilities for `xtask` and `tests`.

pub fn default_flags() -> Vec<String> {
    vec!["--crate-type=rlib".to_string(), "--edition=2021".to_string()]
}
