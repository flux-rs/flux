//! Shared development utilities for `xtask` and `tests`.

use std::{path::PathBuf, str::FromStr};

pub fn default_flags() -> Vec<String> {
    vec!["--crate-type=rlib".to_string(), "--edition=2021".to_string()]
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
