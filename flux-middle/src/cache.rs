use std::{fs::File, path::PathBuf};

use flux_common::config::CONFIG;
use rustc_hash::FxHashMap;
use rustc_span::def_id::DefId;

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

    pub fn insert<Tag>(&mut self, did: DefId, constr_hash: u64) {
        let str = crate::pretty::def_id_to_string(did);
        self.entries.insert(str, constr_hash);
    }

    pub fn is_safe<Tag>(&self, did: DefId, constr_hash: u64) -> bool {
        let str = crate::pretty::def_id_to_string(did);
        self.entries.get(&str).map_or(false, |h| *h == constr_hash)
    }

    fn path() -> Result<PathBuf, std::io::Error> {
        let dir = &CONFIG.log_dir;
        std::fs::create_dir_all(dir)?;
        Ok(dir.join("cache.json"))
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
