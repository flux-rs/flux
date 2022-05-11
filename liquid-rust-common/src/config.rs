use config::Environment;
use serde::Deserialize;
use std::{io::Read, lazy::SyncLazy, path::PathBuf};
pub use toml::Value;

#[derive(Debug, Deserialize, Copy, Clone)]
pub enum AssertBehaviorOptions {
    Ignore,
    Assume,
    Check,
}

impl std::str::FromStr for AssertBehaviorOptions {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "ignore" => Ok(AssertBehaviorOptions::Ignore),
            "assume" => Ok(AssertBehaviorOptions::Assume),
            "check" => Ok(AssertBehaviorOptions::Check),
            _ => Err(()),
        }
    }
}

#[derive(Debug)]
pub struct CrateConfig {
    pub log_dir: PathBuf,
    pub dump_constraint: bool,
    pub dump_checker_trace: bool,
    pub assert_terminator_behavior: AssertBehaviorOptions,
}

#[derive(Deserialize)]
pub struct Config {
    pub log_dir: PathBuf,
    pub dump_constraint: bool,
    pub dump_checker_trace: bool,
    pub assert_terminator_behavior: AssertBehaviorOptions,
}

pub static CONFIG: SyncLazy<Config> = SyncLazy::new(|| {
    fn build() -> Result<Config, config::ConfigError> {
        config::Config::builder()
            .set_default("log_dir", "./log/")?
            .set_default("dump_constraint", false)?
            .set_default("dump_checker_trace", false)?
            .set_default("assert_terminator_behavior", "Assume")?
            .add_source(Environment::with_prefix("LR").ignore_empty(true))
            .build()?
            .try_deserialize()
    }
    build().unwrap()
});

pub static CONFIG_PATH: SyncLazy<Option<PathBuf>> = SyncLazy::new(|| {
    if let Ok(file) = std::env::var("LR_CONFIG") {
        return Some(PathBuf::from(file));
    }

    // find config file in current or parent directories
    let mut path = std::env::current_dir().unwrap();
    loop {
        for name in ["liquid-rust.toml", ".liquid-rust.toml"] {
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

pub static CONFIG_FILE: SyncLazy<Value> = SyncLazy::new(|| {
    if let Some(path) = &*CONFIG_PATH {
        let mut file = std::fs::File::open(path).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents).unwrap();
        toml::from_str(&contents).unwrap()
    } else {
        toml::from_str("").unwrap()
    }
});
