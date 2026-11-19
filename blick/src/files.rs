//! The folder of programs the page can open (`blick <dir>`), e.g. Flux's regression tests.

use std::{io, path::Path};

/// Every `.rs` file under `root`, as `/`-separated paths relative to it, sorted. Hidden entries
/// and `target` directories are skipped.
pub fn list(root: &Path) -> io::Result<Vec<String>> {
    let mut files = vec![];
    walk(root, "", &mut files)?;
    files.sort();
    Ok(files)
}

fn walk(dir: &Path, prefix: &str, files: &mut Vec<String>) -> io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let Ok(name) = entry.file_name().into_string() else { continue };
        if name.starts_with('.') {
            continue;
        }
        let rel = format!("{prefix}{name}");
        // follows symlinks, so a linked folder of tests is listed too
        let path = entry.path();
        if path.is_dir() {
            if name != "target" {
                walk(&path, &format!("{rel}/"), files)?;
            }
        } else if name.ends_with(".rs") {
            files.push(rel);
        }
    }
    Ok(())
}
