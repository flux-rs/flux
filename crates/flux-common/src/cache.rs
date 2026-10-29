use std::{
    fs::{self, File},
    io::BufWriter,
    path::PathBuf,
};

use rustc_hash::FxHashMap;

#[derive(Debug, serde::Serialize, serde::Deserialize)]
struct QueryVal<R> {
    constr_hash: u64,
    result: R,
}

pub struct QueryCache<R> {
    /// Where the cache is saved. `None` if caching is disabled.
    path: Option<PathBuf>,
    entries: FxHashMap<String, QueryVal<R>>,
}

impl<R> Default for QueryCache<R> {
    fn default() -> Self {
        Self::new()
    }
}

impl<R> QueryCache<R> {
    pub fn new() -> Self {
        QueryCache { path: None, entries: FxHashMap::default() }
    }

    pub fn insert(&mut self, key: String, constr_hash: u64, result: R) {
        let val = QueryVal { constr_hash, result };
        self.entries.insert(key, val);
    }

    pub fn lookup(&self, key: &String, constr_hash: u64) -> Option<&R> {
        let val = self.entries.get(key)?;
        if val.constr_hash == constr_hash { Some(&val.result) } else { None }
    }

    /// Look up a result by key only (no hash validation).
    pub fn lookup_by_key(&self, key: &str) -> Option<&R> {
        self.entries.get(key).map(|e| &e.result)
    }

    /// Mutate a cached result by key only (no hash validation).
    pub fn update_result_by_key(&mut self, key: &str, f: impl FnOnce(&mut R)) {
        if let Some(entry) = self.entries.get_mut(key) {
            f(&mut entry.result);
        }
    }
}

impl<R: std::fmt::Debug + serde::Serialize + serde::de::DeserializeOwned> QueryCache<R> {
    /// Saves the cache to the file it was loaded from, overwriting it. Does nothing if the cache
    /// was not loaded from a file.
    pub fn save(&self) -> Result<(), std::io::Error> {
        let Some(path) = &self.path else { return Ok(()) };
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        let file = File::create(path).unwrap();
        serde_json::to_writer(BufWriter::new(file), &self.entries).unwrap();
        Ok(())
    }

    /// Loads the cache from `path`, starting with an empty cache if the file is missing or
    /// invalid. The cache is later saved to the same `path`.
    pub fn load(path: PathBuf) -> Self {
        let entries = fs::read(&path)
            .ok()
            .and_then(|data| serde_json::from_slice(&data).ok())
            .unwrap_or_default();
        QueryCache { path: Some(path), entries }
    }
}
