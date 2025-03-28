use std::{io::Read, path::PathBuf, str::FromStr, sync::LazyLock};

use config::{Environment, File};
use serde::Deserialize;
pub use toml::Value;

const FLUX_ENV_VAR_PREFIX: &str = "FLUX";
const FLUX_CONFIG_ENV_VAR: &str = "FLUX_CONFIG";

pub fn check_def() -> &'static str {
    &CONFIG.check_def
}

pub fn dump_checker_trace() -> bool {
    CONFIG.dump_checker_trace
}

pub fn dump_mir() -> bool {
    CONFIG.dump_mir
}

pub fn dump_constraint() -> bool {
    CONFIG.dump_constraint
}

pub fn dump_fhir() -> bool {
    CONFIG.dump_fhir
}

pub fn dump_rty() -> bool {
    CONFIG.dump_rty
}

pub fn pointer_width() -> PointerWidth {
    CONFIG.pointer_width
}

pub fn log_dir() -> &'static PathBuf {
    &CONFIG.log_dir
}

pub fn is_cache_enabled() -> bool {
    CONFIG.cache
}

pub fn is_checked_file(file: &str) -> bool {
    CONFIG.check_files.is_checked_file(file)
}

pub fn cache_path() -> PathBuf {
    log_dir().join(&CONFIG.cache_file)
}

fn check_overflow() -> bool {
    CONFIG.check_overflow
}

fn scrape_quals() -> bool {
    CONFIG.scrape_quals
}

pub fn smt_define_fun() -> bool {
    CONFIG.smt_define_fun
}

fn solver() -> SmtSolver {
    CONFIG.solver
}

pub fn catch_bugs() -> bool {
    CONFIG.catch_bugs
}

#[derive(Deserialize)]
struct Config {
    log_dir: PathBuf,
    dump_constraint: bool,
    dump_checker_trace: bool,
    dump_fhir: bool,
    dump_rty: bool,
    dump_mir: bool,
    catch_bugs: bool,
    pointer_width: PointerWidth,
    check_def: String,
    check_files: Paths,
    cache: bool,
    cache_file: String,
    check_overflow: bool,
    scrape_quals: bool,
    solver: SmtSolver,
    smt_define_fun: bool,
}

#[derive(Default)]
struct Paths {
    paths: Option<Vec<PathBuf>>,
}

impl Paths {
    fn is_checked_file(&self, file: &str) -> bool {
        self.paths
            .as_ref()
            .is_none_or(|p| p.iter().any(|p| p.to_str().unwrap() == file))
    }
}

impl<'de> Deserialize<'de> for Paths {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let paths: Vec<PathBuf> = String::deserialize(deserializer)?
            .split(",")
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(PathBuf::from)
            .collect();

        let paths = if paths.is_empty() { None } else { Some(paths) };

        Ok(Paths { paths })
    }
}

#[derive(Copy, Clone, Deserialize)]
#[serde(try_from = "u8")]
pub enum PointerWidth {
    W32,
    W64,
}

impl PointerWidth {
    pub fn bits(self) -> u64 {
        match self {
            PointerWidth::W32 => 32,
            PointerWidth::W64 => 64,
        }
    }
}

impl TryFrom<u8> for PointerWidth {
    type Error = &'static str;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            32 => Ok(PointerWidth::W32),
            64 => Ok(PointerWidth::W64),
            _ => Err("pointer width must be 32 or 64"),
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

#[derive(Clone, Copy, Debug, Deserialize, Default)]
#[serde(try_from = "String")]
pub enum SmtSolver {
    #[default]
    Z3,
    CVC5,
}

impl FromStr for SmtSolver {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_ascii_lowercase();
        match s.as_str() {
            "z3" => Ok(SmtSolver::Z3),
            "cvc5" => Ok(SmtSolver::CVC5),
            _ => Err("backend must be one of `z3` or `cvc5`"),
        }
    }
}

impl TryFrom<String> for SmtSolver {
    type Error = &'static str;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        value.parse()
    }
}

static CONFIG: LazyLock<Config> = LazyLock::new(|| {
    fn build() -> Result<Config, config::ConfigError> {
        let mut config_builder = config::Config::builder()
            .set_default("driver_path", None::<String>)?
            .set_default("log_dir", "./log/")?
            .set_default("dump_constraint", false)?
            .set_default("dump_checker_trace", false)?
            .set_default("dump_mir", false)?
            .set_default("dump_fhir", false)?
            .set_default("dump_rty", false)?
            .set_default("catch_bugs", false)?
            .set_default("pointer_width", "64")?
            .set_default("check_def", "")?
            .set_default("check_files", "")?
            .set_default("cache", false)?
            .set_default("cache_file", "cache.json")?
            .set_default("check_overflow", false)?
            .set_default("scrape_quals", false)?
            .set_default("solver", "z3")?
            .set_default("smt_define_fun", false)?;

        // Config comes first, environment settings override it.
        if let Some(config_path) = CONFIG_PATH.as_ref() {
            config_builder = config_builder.add_source(File::from(config_path.clone()));
        };
        config_builder
            .add_source(Environment::with_prefix(FLUX_ENV_VAR_PREFIX).ignore_empty(true))
            .build()?
            .try_deserialize()
    }
    build().unwrap()
});

pub static CONFIG_PATH: LazyLock<Option<PathBuf>> = LazyLock::new(|| {
    if let Ok(file) = std::env::var(FLUX_CONFIG_ENV_VAR) {
        return Some(PathBuf::from(file));
    }

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
});

pub static CONFIG_FILE: LazyLock<Value> = LazyLock::new(|| {
    if let Some(path) = &*CONFIG_PATH {
        let mut file = std::fs::File::open(path).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents).unwrap();
        toml::from_str(&contents).unwrap()
    } else {
        toml::from_str("").unwrap()
    }
});
