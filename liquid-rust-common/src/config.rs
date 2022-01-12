use config::Environment;
use serde::Deserialize;
use std::{lazy::SyncLazy, path::PathBuf};

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
