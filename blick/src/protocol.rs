//! The messages between the server and the page. Their TypeScript types are generated from these
//! definitions (see [`write_bindings`]) into `client/src/bindings`.

use std::{fs, path::Path};

use serde::{Deserialize, Serialize};
use ts_rs::{Config, TS};

/// `GET /api/info`, shown in the page's status line.
#[derive(Serialize, TS)]
pub struct Info {
    pub command: String,
    pub repo: String,
}

/// The first (and only) message the page sends on `/api/run-ws`.
#[derive(Deserialize, TS)]
pub struct RunRequest {
    pub source: String,
    #[serde(default)]
    pub flags: Vec<String>,
}

/// What the server sends on `/api/run-ws`: every output line while `cargo x run` works, then the
/// result.
#[derive(Serialize, TS)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum ServerMsg {
    Line { text: String },
    Done(RunResult),
}

#[derive(Serialize, TS)]
#[serde(rename_all = "lowercase")]
pub enum Stage {
    /// The request was malformed.
    Request,
    /// Building Flux failed.
    Build,
    /// Flux ran on the program.
    Flux,
}

#[derive(Serialize, TS)]
pub struct RunResult {
    /// Whether `cargo x run` exited successfully.
    pub ok: bool,
    /// The exit code; `None` on timeout.
    pub exit: Option<i32>,
    pub stage: Stage,
    /// The diagnostics.
    pub stderr: String,
    /// The checker trace (`log/checker`); empty if Flux did not write one.
    pub trace: String,
    /// Seconds the run took.
    pub elapsed: Option<f64>,
}

/// Writes the TypeScript types of the messages into `dir`, leaving files whose contents did not
/// change untouched (so the client is not rebuilt for nothing).
pub fn write_bindings(dir: &Path) -> anyhow::Result<()> {
    fs::create_dir_all(dir)?;
    let cfg = Config::new();
    write_binding::<Info>(dir, &cfg)?;
    write_binding::<RunRequest>(dir, &cfg)?;
    write_binding::<ServerMsg>(dir, &cfg)?;
    write_binding::<Stage>(dir, &cfg)?;
    write_binding::<RunResult>(dir, &cfg)?;
    Ok(())
}

fn write_binding<T: TS + 'static>(dir: &Path, cfg: &Config) -> anyhow::Result<()> {
    let path = dir.join(T::output_path().expect("derived types have an output path"));
    let contents = T::export_to_string(cfg)?;
    if fs::read_to_string(&path).ok().as_deref() != Some(contents.as_str()) {
        fs::write(&path, contents)?;
    }
    Ok(())
}
