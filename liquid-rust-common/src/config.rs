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
    fn build() -> Result<Config, config::ConfigError> {
        config::Config::builder()
            .set_default("log_dir", "./log/")?
            .set_default("dump_constraint", false)?
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
