use std::{fs::File, path::PathBuf};

use flux_config as config;
use rustc_hash::FxHashMap;

#[derive(Debug, serde::Serialize, serde::Deserialize)]
struct QueryVal<R> {
    constr_hash: u64,
    result: R,
}

pub struct QueryCache<R> {
    entries: FxHashMap<String, QueryVal<R>>,
}

impl<R> Default for QueryCache<R> {
    fn default() -> Self {
        Self::new()
    }
}

impl<R> QueryCache<R> {
    pub fn new() -> Self {
        QueryCache { entries: FxHashMap::default() }
    }

    pub fn insert(&mut self, key: String, constr_hash: u64, result: R) {
        let val = QueryVal { constr_hash, result };
        self.entries.insert(key, val);
    }

    pub fn lookup(&self, key: &String, constr_hash: u64) -> Option<&R> {
        let val = self.entries.get(key)?;
        if val.constr_hash == constr_hash { Some(&val.result) } else { None }
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
}

impl<R: std::fmt::Debug + serde::Serialize + serde::de::DeserializeOwned> QueryCache<R> {
    pub fn save(&self) -> Result<(), std::io::Error> {
        let path = Self::path()?;
        let mut file = File::create(path).unwrap();
        serde_json::to_writer(&mut file, &self.entries).unwrap();
        Ok(())
    }

    pub fn load() -> Self {
        let path = Self::path();
        if let Ok(path) = path {
            if let Ok(file) = File::open(path) {
                let entries = serde_json::from_reader(file);
                if let Ok(entries) = entries {
                    return QueryCache { entries };
                }
            }
        }
        Self::default()
    }
}
