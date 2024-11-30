use std::{fs::File, path::PathBuf};

use flux_config as config;
use rustc_hash::FxHashMap;

#[derive(serde::Serialize, serde::Deserialize)]
pub struct QueryCache {
    /// map from [`DefId`] (as string) to hash of the constraint for that [`DefId`]
    entries: FxHashMap<String, u64>,
    /// map from [`DefId`] (as string) to modification time (at *previous* execution of flux)
    old_timestamps: FxHashMap<String, std::time::SystemTime>,
    /// map from [`DefId`] (as string) to modification time (at *current* execution of flux);
    /// the `DefId` is checked if its `new_timestap` is newer than its `old_timestamp`.
    new_timestamps: FxHashMap<String, std::time::SystemTime>,
}

impl Default for QueryCache {
    fn default() -> Self {
        Self::new()
    }
}

impl QueryCache {
    pub fn new() -> Self {
        QueryCache {
            entries: FxHashMap::default(),
            old_timestamps: FxHashMap::default(),
            new_timestamps: FxHashMap::default(),
        }
    }

    pub fn insert_safe_query(&mut self, key: String, constr_hash: u64) {
        self.entries.insert(key, constr_hash);
    }

    pub fn is_safe_query(&self, key: &String, constr_hash: u64) -> bool {
        config::is_cache_enabled() && self.entries.get(key).map_or(false, |h| *h == constr_hash)
    }

    /// returns `true` if the key is absent or the timestamp is newer or the def_id's constraint was NOT marked safe
    /// If the query was not marked SAFE -- i.e. is not in `.entries` we consider it "modified" to run the checker
    /// to regenerate the error messages.
    pub fn is_modified(&mut self, key: String, timestamp: std::time::SystemTime) -> bool {
        let old = self.old_timestamps.get(&key);
        let was_safe = self.entries.contains_key(&key);
        println!("TRACE: is_modified {key:?} {old:?} {timestamp:?}");
        self.new_timestamps.insert(key, timestamp);
        if let Some(old_timestamp) = old {
            if *old_timestamp == timestamp && was_safe {
                return false;
            }
        }
        return true;
    }

    fn path() -> Result<PathBuf, std::io::Error> {
        if config::is_cache_enabled() || config::check_diff() {
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
        serde_json::to_writer(&mut file, &self.to_jsonable_tuple()).unwrap();
        Ok(())
    }

    // FIXME: silly hack to get around serde::Serialize shenanigans
    fn to_jsonable_tuple(
        &self,
    ) -> (FxHashMap<String, u64>, FxHashMap<String, std::time::SystemTime>) {
        (self.entries.clone(), self.new_timestamps.clone())
    }

    // FIXME: silly hack to get around serde::Deserialize shenanigans
    fn from_jsonable_tuple(
        tuple: (FxHashMap<String, u64>, FxHashMap<String, std::time::SystemTime>),
    ) -> Self {
        QueryCache {
            entries: tuple.0,
            old_timestamps: tuple.1,
            new_timestamps: FxHashMap::default(),
        }
    }

    pub fn load() -> Self {
        if let Ok(path) = Self::path() {
            if let Ok(file) = File::open(path) {
                if let Ok(data) = serde_json::from_reader(file) {
                    println!("TRACE: loaded cache");
                    return Self::from_jsonable_tuple(data);
                }
            }
        }
        Self::default()
    }
}
