use std::{fs::File, path::PathBuf};

use flux_config as config;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::FileName;

#[derive(serde::Serialize, serde::Deserialize)]
pub struct QueryCache {
    /// map from [`DefId`] (as string) to hash of the constraint for that [`DefId`]
    entries: FxHashMap<String, Option<u64>>,
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

    pub fn insert_safe_query(
        &mut self,
        tcx: &TyCtxt,
        def_id: LocalDefId,
        constr_hash: Option<u64>,
    ) {
        let key = tcx.def_path_str(def_id);
        self.entries.insert(key, constr_hash);
    }

    pub fn is_safe_query(&self, tcx: &TyCtxt, def_id: LocalDefId, constr_hash: u64) -> bool {
        let key = tcx.def_path_str(def_id);
        config::is_cache_enabled()
            && self
                .entries
                .get(&key)
                .map_or(false, |h| *h == Some(constr_hash))
    }

    pub fn is_safe_def_id(&self, tcx: &TyCtxt, def_id: LocalDefId) -> bool {
        let key = tcx.def_path_str(def_id);
        self.entries.contains_key(&key)
    }

    /// returns `Some((key, timestamp))` if the path exists,
    /// with `key` as a string representation of the `path`
    /// and `timestamp` as most recent known modification time for that path.
    fn get_path_timestamp(
        &mut self,
        path: &std::path::Path,
    ) -> Option<(String, std::time::SystemTime)> {
        let key = path.to_string_lossy().to_string();
        match self.new_timestamps.get(&key) {
            Some(t) => Some((key, *t)),
            None => {
                if let Ok(metadata) = std::fs::metadata(path) {
                    if let Ok(modified_time) = metadata.modified() {
                        self.new_timestamps.insert(key.clone(), modified_time);
                        return Some((key, modified_time));
                    }
                }
                None
            }
        }
    }

    fn get_def_id_timestamp(
        &mut self,
        tcx: &TyCtxt,
        def_id: LocalDefId,
    ) -> Option<(String, std::time::SystemTime)> {
        let span = tcx.def_span(def_id);
        let sm = tcx.sess.source_map();
        if let FileName::Real(file_name) = sm.span_to_filename(span) {
            if let Some(path) = file_name.local_path() {
                return self.get_path_timestamp(path);
            }
        }
        None
    }

    /// returns `true` if the key is absent or the timestamp is newer or the def_id's constraint was NOT marked safe
    /// If the query was not marked SAFE -- i.e. is not in `.entries` we consider it "modified" so that we can run
    /// the checker to regenerate the error messages.
    pub fn is_modified(&mut self, tcx: &TyCtxt, def_id: LocalDefId) -> bool {
        if let Some((key, timestamp)) = self.get_def_id_timestamp(tcx, def_id) {
            let old_timestamp = self.old_timestamps.get(&key);
            let was_safe = self.entries.contains_key(&tcx.def_path_str(def_id));
            if let Some(old_timestamp) = old_timestamp {
                let is_same_timestamp = *old_timestamp == timestamp;
                if is_same_timestamp && was_safe {
                    return false;
                }
            }
        }
        true
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
        serde_json::to_writer(&mut file, &self.to_jsonable_tuple()).unwrap();
        Ok(())
    }

    // FIXME: silly hack to get around serde::Serialize shenanigans
    fn to_jsonable_tuple(
        &self,
    ) -> (FxHashMap<String, Option<u64>>, FxHashMap<String, std::time::SystemTime>) {
        // we update the old timestamps with the new ones so as to *preserve* the old timestamps
        // for files that were *not checked* in this current round for whatever `rustc` reason,
        // e.g. they were cached, there were other errors etc. We want to save these too to avoid
        // rechecking those files in subsequent runs (unless of course, those files are edited by then.)
        let mut timestamps = self.old_timestamps.clone();
        for (k, v) in &self.new_timestamps {
            timestamps.insert(k.clone(), *v);
        }
        (self.entries.clone(), timestamps)
    }

    // FIXME: silly hack to get around serde::Deserialize shenanigans
    fn from_jsonable_tuple(
        tuple: (FxHashMap<String, Option<u64>>, FxHashMap<String, std::time::SystemTime>),
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
                    return Self::from_jsonable_tuple(data);
                }
            }
        }
        Self::default()
    }
}
