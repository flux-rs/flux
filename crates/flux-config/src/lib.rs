#![feature(if_let_guard)]
use globset::{Glob, GlobSet, GlobSetBuilder};
pub use toml::Value;
use tracing::Level;
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

pub fn dump_checker_trace_info() -> bool {
    match FLAGS.dump_checker_trace {
        Some(l) => Level::INFO <= l,
        None => false,
    }
}

pub fn dump_checker_trace() -> Option<Level> {
    FLAGS.dump_checker_trace
}

pub fn dump_constraint() -> bool {
    FLAGS.dump_constraint
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

pub fn trusted_default() -> bool {
    FLAGS.trusted_default
}

pub fn ignore_default() -> bool {
    FLAGS.ignore_default
}

pub fn emit_lean_defs() -> bool {
    FLAGS.emit_lean_defs
}

pub fn cache_path() -> Option<&'static Path> {
    FLAGS.cache.as_deref()
}

pub fn include_pattern() -> Option<&'static IncludePattern> {
    FLAGS.include.as_ref()
}

fn check_overflow() -> OverflowMode {
    FLAGS.check_overflow
}

pub fn allow_uninterpreted_cast() -> bool {
    FLAGS.allow_uninterpreted_cast
}

fn scrape_quals() -> bool {
    FLAGS.scrape_quals
}

pub fn no_panic() -> bool {
    FLAGS.no_panic
}

pub fn smt_define_fun() -> bool {
    FLAGS.smt_define_fun
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

pub fn summary() -> bool {
    FLAGS.summary
}

pub fn full_compilation() -> bool {
    FLAGS.full_compilation
}

pub fn save_user_interactions() -> bool {
    FLAGS.save_user_interactions
}

pub fn user_interactions_file() -> Option<&'static PathBuf> {
    FLAGS.user_interactions_file.as_ref()
}

pub fn no_suggestions_default() -> bool {
    FLAGS.no_suggestions_default
}

#[derive(Clone, Debug, Deserialize)]
#[serde(try_from = "String")]
pub struct Pos {
    pub file: String,
    pub line: usize,
    pub column: usize,
}

impl FromStr for Pos {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        let parts: Vec<&str> = s.split(':').collect();
        if parts.len() != 3 {
            return Err("span format should be '<file>:<line>:<column>'");
        }
        let file = parts[0].to_string();
        let line = parts[1]
            .parse::<usize>()
            .map_err(|_| "invalid line number")?;
        let column = parts[2]
            .parse::<usize>()
            .map_err(|_| "invalid column number")?;
        Ok(Pos { file, line, column })
    }
}

impl TryFrom<String> for Pos {
    type Error = &'static str;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        value.parse()
    }
}

impl fmt::Display for IncludePattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        write!(f, "glob:{:?},", self.glob)?;
        for def in &self.defs {
            write!(f, "def:{},", def)?;
        }
        for pos in &self.spans {
            write!(f, "span:{}:{}:{}", pos.file, pos.line, pos.column)?;
        }
        write!(f, "]")?;
        Ok(())
    }
}
/// This specifies which `DefId` should be checked. It can be specified via multiple patterns
/// of the form `-Finclude=<pattern>` and the `DefId` is checked if it matches *any* of the patterns.
/// Patterns are checked relative to the current working directory.
#[derive(Clone)]
pub struct IncludePattern {
    /// files matching the glob pattern, e.g. `glob:src/ascii/*.rs` to check all files in the `ascii` module
    pub glob: GlobSet,
    /// defs (`fn`, `enum`, ...) matching the given function name as a substring, e.g. `def:watermelon`
    pub defs: Vec<String>,
    /// fn whose implementation overlaps the file, line, e.g. `span:tests/tests/pos/detached/detach00.rs:13:3`
    pub spans: Vec<Pos>,
}

impl IncludePattern {
    fn new(includes: Vec<String>) -> Result<Self, String> {
        let mut defs = Vec::new();
        let mut spans = Vec::new();
        let mut glob = GlobSetBuilder::new();
        for include in includes {
            if let Some(suffix) = include.strip_prefix("def:") {
                defs.push(suffix.to_string());
            } else if let Some(suffix) = include.strip_prefix("span:") {
                spans.push(Pos::from_str(suffix)?);
            } else {
                let suffix = include.strip_prefix("glob:").unwrap_or(&include);
                let glob_pattern = Glob::new(suffix.trim()).map_err(|_| "invalid glob pattern")?;
                glob.add(glob_pattern);
            }
        }
        let glob = glob.build().map_err(|_| "failed to build glob set")?;
        Ok(IncludePattern { glob, defs, spans })
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Default)]
#[serde(try_from = "String")]
pub enum OverflowMode {
    /// Strict-Underflow, No overflow checking
    #[default]
    None,
    /// Lazy underflow, Lazy overflow checking; lose all information
    /// unless values are known to be in valid range
    Lazy,
    /// Strict underflow, Lazy overflow checking; always check
    /// unsignedness (non-negativity) but lazy for upper-bound
    StrictUnder,
    /// Strict underflow, Strict overflow checking; always check
    /// values in valid range for type
    Strict,
}

impl OverflowMode {
    const ERROR: &'static str = "expected one of `none`, `lazy`, or `strict`";
}
impl FromStr for OverflowMode {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_ascii_lowercase();
        match s.as_str() {
            "none" => Ok(OverflowMode::None),
            "lazy" => Ok(OverflowMode::Lazy),
            "strict" => Ok(OverflowMode::Strict),
            "strict-under" => Ok(OverflowMode::StrictUnder),
            _ => Err(Self::ERROR),
        }
    }
}

impl TryFrom<String> for OverflowMode {
    type Error = &'static str;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        value.parse()
    }
}

impl fmt::Display for OverflowMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OverflowMode::None => write!(f, "none"),
            OverflowMode::Lazy => write!(f, "lazy"),
            OverflowMode::Strict => write!(f, "strict"),
            OverflowMode::StrictUnder => write!(f, "strict-under"),
        }
    }
}

pub fn debug_binder_output() -> bool {
    FLAGS.debug_binder_output
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
    pub check_overflow: OverflowMode,
    /// Whether qualifiers should be scraped from the constraint.
    pub scrape_quals: bool,
    pub solver: SmtSolver,
    /// Whether to allow uninterpreted casts (e.g., from some random `S` to `int`).
    pub allow_uninterpreted_cast: bool,
}

impl From<PartialInferOpts> for InferOpts {
    fn from(opts: PartialInferOpts) -> Self {
        InferOpts {
            check_overflow: opts.check_overflow.unwrap_or_else(check_overflow),
            scrape_quals: opts.scrape_quals.unwrap_or_else(scrape_quals),
            solver: opts.solver.unwrap_or_else(solver),
            allow_uninterpreted_cast: opts
                .allow_uninterpreted_cast
                .unwrap_or_else(allow_uninterpreted_cast),
        }
    }
}

#[derive(Clone, Copy, Default, Deserialize, Debug)]
pub struct PartialInferOpts {
    pub check_overflow: Option<OverflowMode>,
    pub scrape_quals: Option<bool>,
    pub solver: Option<SmtSolver>,
    pub allow_uninterpreted_cast: Option<bool>,
}

impl PartialInferOpts {
    pub fn merge(&mut self, other: &Self) {
        self.check_overflow = self.check_overflow.or(other.check_overflow);
        self.allow_uninterpreted_cast = self
            .allow_uninterpreted_cast
            .or(other.allow_uninterpreted_cast);
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
