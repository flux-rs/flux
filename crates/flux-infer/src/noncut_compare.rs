//! Side-by-side dump of Flux's local non-cut KVar solutions vs. fixpoint's, for
//! one task at a time.
//!
//! Activated by `FLUX_NONCUT_COMPARE=<dir>`. When set, [`enabled`] returns the
//! directory; in that case the encoder is expected to:
//!
//! 1. Capture Flux's local view via `Constraint::non_cut_solution_strings()`
//!    on the *un-eliminated* constraint.
//! 2. Ship the un-eliminated constraint to fixpoint.
//! 3. Call [`record`] with the task key, the captured Flux solutions, and
//!    fixpoint's `non_cuts_solution` from the verification result.
//!
//! Each call writes one human-readable file under `<dir>/<sanitized_key>.txt`
//! listing every non-cut kvar that either side reported, with the two views
//! side-by-side.

use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
    sync::Mutex,
};

use rustc_hash::FxHashMap;

static DIR_LOCK: Mutex<()> = Mutex::new(());

/// Returns the directory if `FLUX_NONCUT_COMPARE` is set, otherwise None.
pub(crate) fn enabled() -> Option<PathBuf> {
    std::env::var_os("FLUX_NONCUT_COMPARE").map(PathBuf::from)
}

/// Sanitize a task key into a filesystem-safe filename.
fn sanitize(key: &str) -> String {
    key.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '.' || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Each entry is `(kvar_name, list_of_per_cube_strings)`.
pub(crate) type FluxSolutions = Vec<(String, Vec<String>)>;

/// Each entry is `(kvar_name, fixpoint_solution_string)`.
pub(crate) type FixpointSolutions = Vec<(String, String)>;

pub(crate) fn record(
    dir: &Path,
    task_key: &str,
    flux: FluxSolutions,
    fixpoint: FixpointSolutions,
) {
    let _guard = DIR_LOCK.lock().unwrap();
    if let Err(e) = fs::create_dir_all(dir) {
        eprintln!("[noncut-compare] cannot create {dir:?}: {e}");
        return;
    }

    // Index both sides by kvar name.
    let mut flux_by_k: FxHashMap<String, Vec<String>> = FxHashMap::default();
    for (k, sols) in flux {
        flux_by_k.insert(k, sols);
    }
    let mut fp_by_k: FxHashMap<String, String> = FxHashMap::default();
    for (k, sol) in fixpoint {
        fp_by_k.insert(k, sol);
    }

    // Union of kvar names, sorted for stable output.
    let mut all_kvars: Vec<String> = flux_by_k.keys().chain(fp_by_k.keys()).cloned().collect();
    all_kvars.sort();
    all_kvars.dedup();

    let mut out = String::new();
    out.push_str("task_key: ");
    out.push_str(task_key);
    out.push_str("\nnon-cut kvars: ");
    out.push_str(&all_kvars.len().to_string());
    out.push_str("\n");

    for k in &all_kvars {
        out.push_str("\n========================================\n");
        out.push_str(&format!("kvar: {k}\n"));
        out.push_str("----------------------------------------\n");
        out.push_str("flux local solution (cube preds):\n");
        match flux_by_k.get(k) {
            Some(cubes) if !cubes.is_empty() => {
                for (i, cube) in cubes.iter().enumerate() {
                    out.push_str(&format!("  [cube {i}] {cube}\n"));
                }
            }
            Some(_) => out.push_str("  (none — flux has no cubes for this kvar)\n"),
            None => out.push_str("  (kvar not in flux's non-cut set)\n"),
        }
        out.push_str("----------------------------------------\n");
        out.push_str("fixpoint nonCutsSolution:\n");
        match fp_by_k.get(k) {
            Some(sol) => out.push_str(&format!("  {sol}\n")),
            None => out.push_str("  (kvar not in fixpoint's non-cut set)\n"),
        }
    }

    let path = dir.join(format!("{}.txt", sanitize(task_key)));
    match fs::OpenOptions::new().create(true).write(true).truncate(true).open(&path) {
        Ok(mut f) => {
            if let Err(e) = f.write_all(out.as_bytes()) {
                eprintln!("[noncut-compare] write {path:?} failed: {e}");
            }
        }
        Err(e) => eprintln!("[noncut-compare] open {path:?} failed: {e}"),
    }
}
