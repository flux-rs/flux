use config::Environment;
use serde::Deserialize;
use std::{io::Read, lazy::SyncLazy, path::PathBuf};
pub use toml::Value;

#[derive(Deserialize)]
pub struct Config {
    pub log_dir: PathBuf,
    pub dump_constraint: bool,
}

pub static CONFIG: SyncLazy<Config> = SyncLazy::new(|| {
    let mut config = config::Config::new();
    // 1. Set defaults
    config.set_default("log_dir", "./log/").unwrap();
    config.set_default("dump_constraint", false).unwrap();

    // 2. Merge with env variables (prefixed with LR_)
    config
        .merge(Environment::with_prefix("LR").ignore_empty(true))
        .unwrap();

    config.try_into().unwrap()
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
