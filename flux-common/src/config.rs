use std::{io::Read, path::PathBuf, sync::LazyLock};

use config::{Environment, File};
use serde::Deserialize;
pub use toml::Value;

const FLUX_ENV_VAR_PREFIX: &str = "FLUX";
const FLUX_CONFIG_ENV_VAR: &str = "FLUX_CONFIG";

#[derive(Debug, Deserialize, Copy, Clone)]
#[serde(rename_all = "lowercase")]
pub enum AssertBehavior {
    Ignore,
    Assume,
    Check,
}

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

pub fn pointer_width() -> u64 {
    CONFIG.pointer_width
}

pub fn assert_behavior() -> AssertBehavior {
    CONFIG.check_asserts
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

pub fn driver_path() -> Option<&'static PathBuf> {
    CONFIG.path.as_ref()
}

impl std::str::FromStr for AssertBehavior {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "ignore" => Ok(AssertBehavior::Ignore),
            "assume" => Ok(AssertBehavior::Assume),
            "check" => Ok(AssertBehavior::Check),
            _ => Err(()),
        }
    }
}

#[derive(Debug)]
pub struct CrateConfig {
    pub log_dir: PathBuf,
    pub dump_constraint: bool,
    pub dump_checker_trace: bool,
    pub check_asserts: AssertBehavior,
}

#[derive(Deserialize)]
struct Config {
    path: Option<PathBuf>,
    log_dir: PathBuf,
    dump_constraint: bool,
    dump_checker_trace: bool,
    dump_timings: bool,
    check_asserts: AssertBehavior,
    dump_mir: bool,
    pointer_width: u64,
    check_def: String,
    cache: bool,
    cache_file: String,
}

static CONFIG: LazyLock<Config> = LazyLock::new(|| {
    fn build() -> Result<Config, config::ConfigError> {
        let mut config_builder = config::Config::builder()
            .set_default("path", None::<String>)?
            .set_default("log_dir", "./log/")?
            .set_default("dump_constraint", false)?
            .set_default("dump_checker_trace", false)?
            .set_default("dump_timings", false)?
            .set_default("dump_mir", false)?
            .set_default("check_asserts", "assume")?
            .set_default("pointer_width", 64)?
            .set_default("check_def", "")?
            .set_default("cache", false)?
            .set_default("cache_file", "cache.json")?;
        // Config comes first, enviroment settings override it.
        if let Some(config_path) = CONFIG_PATH.as_ref() {
            config_builder = config_builder.add_source(File::from(config_path.to_path_buf()));
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
