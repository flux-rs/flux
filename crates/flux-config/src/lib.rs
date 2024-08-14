use std::{io::Read, path::PathBuf, sync::LazyLock};

use config::{Environment, File};
use serde::Deserialize;
pub use toml::Value;

const FLUX_ENV_VAR_PREFIX: &str = "FLUX";
const FLUX_CONFIG_ENV_VAR: &str = "FLUX_CONFIG";

pub fn check_def() -> &'static str {
    &CONFIG.check_def
}

pub fn dump_timings() -> bool {
    CONFIG.dump_timings
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

pub fn cache_path() -> PathBuf {
    log_dir().join(&CONFIG.cache_file)
}

pub fn check_overflow() -> bool {
    CONFIG.check_overflow
}

pub fn scrape_quals() -> bool {
    CONFIG.scrape_quals
}

pub fn catch_bugs() -> bool {
    CONFIG.catch_bugs
}

#[derive(Debug, Clone, Copy)]
pub struct CrateConfig {
    pub check_overflow: bool,
    pub scrape_quals: bool,
}

#[derive(Deserialize)]
struct Config {
    log_dir: PathBuf,
    dump_constraint: bool,
    dump_checker_trace: bool,
    dump_timings: bool,
    dump_fhir: bool,
    dump_rty: bool,
    dump_mir: bool,
    catch_bugs: bool,
    pointer_width: PointerWidth,
    check_def: String,
    cache: bool,
    cache_file: String,
    check_overflow: bool,
    scrape_quals: bool,
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

static CONFIG: LazyLock<Config> = LazyLock::new(|| {
    fn build() -> Result<Config, config::ConfigError> {
        let mut config_builder = config::Config::builder()
            .set_default("driver_path", None::<String>)?
            .set_default("log_dir", "./log/")?
            .set_default("dump_constraint", false)?
            .set_default("dump_checker_trace", false)?
            .set_default("dump_timings", false)?
            .set_default("dump_mir", false)?
            .set_default("dump_fhir", false)?
            .set_default("dump_rty", false)?
            .set_default("catch_bugs", false)?
            .set_default("check_asserts", "assume")?
            .set_default("pointer_width", "64")?
            .set_default("check_def", "")?
            .set_default("cache", false)?
            .set_default("cache_file", "cache.json")?
            .set_default("check_overflow", false)?
            .set_default("scrape_quals", false)?;
        // Config comes first, enviroment settings override it.
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

impl Default for CrateConfig {
    fn default() -> Self {
        Self { check_overflow: check_overflow(), scrape_quals: scrape_quals() }
    }
}
