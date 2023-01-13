use std::{fs::File, path::PathBuf};

use rustc_hash::FxHashMap;

use crate::config;

pub struct QueryCache {
    entries: FxHashMap<String, u64>,
}

impl Default for QueryCache {
    fn default() -> Self {
        Self::new()
    }
}

impl QueryCache {
    pub fn new() -> Self {
        QueryCache { entries: FxHashMap::default() }
    }

    pub fn insert(&mut self, key: String, constr_hash: u64) {
        self.entries.insert(key, constr_hash);
    }

    pub fn is_safe(&self, key: &String, constr_hash: u64) -> bool {
        config::is_cache_enabled() && self.entries.get(key).map_or(false, |h| *h == constr_hash)
    }

    fn path() -> Result<PathBuf, std::io::Error> {
        if config::is_cache_enabled() {
            let path = config::cache_path();
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)?;
                return Ok(path);
            }
        }
        Err(Self::no_cache_err())
    }

    fn no_cache_err() -> std::io::Error {
        std::io::Error::new(std::io::ErrorKind::Other, "cache not enabled")
    }

    pub fn save(&self) -> Result<(), std::io::Error> {
        let path = Self::path()?;
        let mut file = File::create(path).unwrap();
        serde_json::to_writer(&mut file, &self.entries).unwrap();
        Ok(())
    }

    pub fn load() -> Self {
        if let Ok(path) = Self::path() {
            if let Ok(file) = File::open(path) {
                if let Ok(entries) = serde_json::from_reader(file) {
                    return QueryCache { entries };
                }
            }
        }
        Self::default()
    }
}
