#![feature(if_let_guard)]
pub use toml::Value;
pub mod flags;

use std::{
    fmt,
    io::Read,
    path::{Path, PathBuf},
    str::FromStr,
    sync::LazyLock,
};

use flags::FLAGS;
use serde::Deserialize;

pub fn check_def() -> &'static str {
    &FLAGS.check_def
}

pub fn dump_checker_trace() -> bool {
    FLAGS.dump_checker_trace
}

pub fn dump_mir() -> bool {
    true
}

pub fn dump_constraint() -> bool {
    true
}

pub fn dump_fhir() -> bool {
    FLAGS.dump_fhir
}

pub fn dump_rty() -> bool {
    FLAGS.dump_rty
}

pub fn pointer_width() -> PointerWidth {
    FLAGS.pointer_width
}

pub fn log_dir() -> &'static PathBuf {
    &FLAGS.log_dir
}

pub fn is_cache_enabled() -> bool {
    FLAGS.cache.is_some()
}

pub fn is_checked_file(file: &str) -> bool {
    FLAGS.check_files.is_checked_file(file)
}

pub fn cache_path() -> Option<&'static Path> {
    FLAGS.cache.as_deref()
}

fn check_overflow() -> bool {
    FLAGS.check_overflow
}

fn scrape_quals() -> bool {
    FLAGS.scrape_quals
}

pub fn smt_define_fun() -> bool {
    FLAGS.smt_define_fun
}

pub fn verbose() -> bool {
    FLAGS.verbose
}

fn solver() -> SmtSolver {
    FLAGS.solver
}

pub fn catch_bugs() -> bool {
    FLAGS.catch_bugs
}

pub fn annots() -> bool {
    FLAGS.annots
}

pub fn timings() -> bool {
    FLAGS.timings
}

pub fn verify() -> bool {
    FLAGS.verify
}

pub fn full_compilation() -> bool {
    FLAGS.full_compilation
}

#[derive(Clone, Copy, Debug, Deserialize, Default)]
#[serde(try_from = "String")]
pub enum SmtSolver {
    #[default]
    Z3,
    CVC5,
}

impl SmtSolver {
    const ERROR: &'static str = "expected one of `z3` or `cvc5`";
}

impl FromStr for SmtSolver {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_ascii_lowercase();
        match s.as_str() {
            "z3" => Ok(SmtSolver::Z3),
            "cvc5" => Ok(SmtSolver::CVC5),
            _ => Err(Self::ERROR),
        }
    }
}

impl TryFrom<String> for SmtSolver {
    type Error = &'static str;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        value.parse()
    }
}

impl fmt::Display for SmtSolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtSolver::Z3 => write!(f, "z3"),
            SmtSolver::CVC5 => write!(f, "cvc5"),
        }
    }
}

/// Options that change the behavior of refinement type inference locally
#[derive(Clone, Copy, Debug)]
pub struct InferOpts {
    /// Enable overflow checking. This affects the signature of primitive operations and the
    /// invariants assumed for primitive types.
    pub check_overflow: bool,
    /// Whether qualifiers should be scraped from the constraint.
    pub scrape_quals: bool,
    pub solver: SmtSolver,
}

impl From<PartialInferOpts> for InferOpts {
    fn from(opts: PartialInferOpts) -> Self {
        InferOpts {
            check_overflow: opts.check_overflow.unwrap_or_else(check_overflow),
            scrape_quals: opts.scrape_quals.unwrap_or_else(scrape_quals),
            solver: opts.solver.unwrap_or_else(solver),
        }
    }
}

#[derive(Clone, Copy, Default, Deserialize, Debug)]
pub struct PartialInferOpts {
    pub check_overflow: Option<bool>,
    pub scrape_quals: Option<bool>,
    pub solver: Option<SmtSolver>,
}

impl PartialInferOpts {
    pub fn merge(&mut self, other: &Self) {
        self.check_overflow = self.check_overflow.or(other.check_overflow);
        self.scrape_quals = self.scrape_quals.or(other.scrape_quals);
        self.solver = self.solver.or(other.solver);
    }
}

#[derive(Copy, Clone, Deserialize, Default)]
pub enum PointerWidth {
    W32,
    #[default]
    W64,
}

impl PointerWidth {
    const ERROR: &str = "pointer width must be 32 or 64";

    pub fn bits(self) -> u64 {
        match self {
            PointerWidth::W32 => 32,
            PointerWidth::W64 => 64,
        }
    }
}

impl FromStr for PointerWidth {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "32" => Ok(PointerWidth::W32),
            "64" => Ok(PointerWidth::W64),
            _ => Err(Self::ERROR),
        }
    }
}

fn config_path() -> Option<PathBuf> {
    // find config file in current or parent directories
    let mut path = std::env::current_dir().unwrap();
    loop {
        for name in ["flux.toml", ".flux.toml"] {
            let file = path.join(name);
            if file.exists() {
                return Some(file);
            }
        }
        if !path.pop() {
            return None;
        }
    }
}

pub static CONFIG_FILE: LazyLock<Value> = LazyLock::new(|| {
    if let Some(path) = config_path() {
        let mut file = std::fs::File::open(path).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents).unwrap();
        toml::from_str(&contents).unwrap()
    } else {
        toml::from_str("").unwrap()
    }
});
