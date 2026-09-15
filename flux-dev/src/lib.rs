//! Shared development utilities for `xtask` and `tests`.

use std::{
    path::{Path, PathBuf},
    str::FromStr,
};

pub fn default_flags(sysroot: &Path, extern_args: Vec<String>) -> Vec<String> {
    let mut flags = vec![
        "--crate-type=rlib".to_string(),
        "--edition=2021".to_string(),
        // Transitive deps ignore `--extern`, so they still need a search path.
        "-L".to_string(),
        sysroot.display().to_string(),
    ];
    flags.extend(extern_args);
    flags.push("-Fverify=on".to_string());
    flags.push(format!("-Fsysroot={}", sysroot.display()));
    flags
}

#[derive(Clone, Copy, Debug)]
pub enum Suite {
    Basic,
    WithDeps,
}

impl Suite {
    pub const ALL: &[Suite] = &[Suite::Basic, Suite::WithDeps];

    pub fn name(self) -> &'static str {
        match self {
            Suite::Basic => "basic",
            Suite::WithDeps => "with-deps",
        }
    }

    pub fn pos_tests(self) -> PathBuf {
        match self {
            Suite::Basic => ["tests", "pos"].iter().collect(),
            Suite::WithDeps => ["tests", "with_deps", "pos"].iter().collect(),
        }
    }

    pub fn neg_tests(self) -> PathBuf {
        match self {
            Suite::Basic => ["tests", "neg"].iter().collect(),
            Suite::WithDeps => ["tests", "with_deps", "neg"].iter().collect(),
        }
    }
}

impl FromStr for Suite {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "basic" => Ok(Suite::Basic),
            "with-deps" => Ok(Suite::WithDeps),
            _ => Err("expected one of: basic, with-deps"),
        }
    }
}
