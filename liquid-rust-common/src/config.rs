//! Utilities for interacting with Liquid Rust configuration.

use config::{Config, ConfigError, Environment, Source, Value};
use itertools::Itertools;
use std::collections::HashMap;
use std::env;

pub const CMD_PREFIX: &'static str = "-L";

lazy_static::lazy_static! {
    static ref SETTINGS: Config = {
        let mut settings = Config::new();

        // 1. Set defaults
        settings.set_default("print_debug", false).unwrap();
        settings.set_default("dump_constraint", "").unwrap();

        // 2. Merge with env variables (prefixed with LR_)
        settings.merge(
            Environment::with_prefix("LR").ignore_empty(true)
        ).unwrap();

        // 3. Merge command line args
        settings.merge(
            CommandLine::new().prefix(CMD_PREFIX)
        ).unwrap();

        settings
    };
}

#[derive(Clone, Debug)]
pub struct CommandLine {
    prefix: Option<String>,
}

impl CommandLine {
    pub fn new() -> Self {
        CommandLine {
            prefix: None,
        }
    }

    pub fn prefix(mut self, s: &str) -> Self {
        self.prefix = Some(s.to_owned());
        self
    }

    fn get_prefix(&self) -> String {
        match self.prefix {
            Some(ref prefix) => prefix.to_owned(),
            _ => String::default(),
        }
    }
}

impl Source for CommandLine {
    fn clone_into_box(&self) -> Box<dyn Source + Send + Sync> {
        Box::new((*self).clone())
    }

    fn collect(&self) -> Result<HashMap<String, Value>, ConfigError> {
        let mut res = HashMap::new();
        let uri = "command-line".to_owned();

        for arg in env::args() {
            if arg.starts_with(&self.get_prefix()) {
                let (key, val) = arg
                    .get(self.get_prefix().len()..)
                    .ok_or_else(|| ConfigError::Message(format!("invalid command line arg: {}", arg)))?
                    .splitn(2, '=')
                    .map(|s| s.to_owned())
                    .next_tuple()
                    .ok_or_else(|| ConfigError::Message(format!("invalid command line arg: {}", arg)))?;

                res.insert(
                    key.to_lowercase(),
                    Value::new(Some(&uri), val),
                );
            }
        }

        Ok(res)
    }
}

pub fn print_debug() -> bool {
    SETTINGS.get_bool("print_debug").unwrap()
}

pub fn should_dump_constraint() -> bool {
    !SETTINGS.get_str("dump_constraint").unwrap().is_empty()
}

pub fn dump_constraint() -> String {
    SETTINGS.get_str("dump_constraint").unwrap()
}
