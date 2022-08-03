use config::Environment;
use serde::Deserialize;
use std::{io::Read, path::PathBuf, sync::LazyLock};
pub use toml::Value;

// serde small case
#[derive(Debug, Deserialize, Copy, Clone)]
#[serde(rename_all = "lowercase")]
pub enum AssertBehavior {
    Ignore,
    Assume,
    Check,
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
pub struct Config {
    pub log_dir: PathBuf,
    pub dump_constraint: bool,
    pub dump_checker_trace: bool,
    pub check_asserts: AssertBehavior,
    pub dump_mir: bool,
}

pub static CONFIG: LazyLock<Config> = LazyLock::new(|| {
    fn build() -> Result<Config, config::ConfigError> {
        config::Config::builder()
            .set_default("log_dir", "./log/")?
            .set_default("dump_constraint", false)?
            .set_default("dump_checker_trace", false)?
            .set_default("dump_mir", false)?
            .set_default("check_asserts", "assume")?
            .add_source(Environment::with_prefix("LR").ignore_empty(true))
            .build()?
            .try_deserialize()
    }
    build().unwrap()
});

pub static CONFIG_PATH: LazyLock<Option<PathBuf>> = LazyLock::new(|| {
    if let Ok(file) = std::env::var("LR_CONFIG") {
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
