//! Loading of `.flux/config.toml`, the configuration of a `cargo flux` invocation.
//!
//! Configuration files are discovered and merged following the same rules cargo uses for
//! `.cargo/config.toml`:
//!
//! * Starting from the current directory, `.flux/config.toml` is read in every ancestor directory,
//!   followed by `$FLUX_HOME/config.toml` (`~/.flux/config.toml` by default) if it wasn't already
//!   found.
//! * Files closer to the current directory take precedence. Tables are merged key by key, arrays
//!   are concatenated (with items from higher precedence files placed later), and any other value
//!   is replaced.
//! * Relative paths are resolved relative to the parent of the directory containing the file,
//!   e.g., a path in `/project/.flux/config.toml` is relative to `/project`.
//!

mod value;

use std::{env, fs};

use cargo_metadata::camino::{Utf8Path, Utf8PathBuf};
use flux_sysroot::flux_home_dir;
use serde::Deserialize;
use value::ConfigValue;
pub use value::{Located, Location};

/// The merged content of all configuration files.
#[derive(Debug, Default)]
pub struct FluxConfig {
    pub settings: Settings,
}

/// Settings that are translated into flags for the driver.
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct Settings {
    pub cache: Cache,
    pub fixpoint: Fixpoint,
    pub diagnostics: Diagnostics,
    pub stats: Stats,
    pub debug: Debug,
}

#[derive(Clone, Debug, Default, Deserialize)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct Cache {
    /// Enables fixpoint query caching.
    pub enabled: Option<bool>,
    /// Directory where cache files are saved. Defaults to `<target-dir>/flux-cache`.
    pub dir: Option<Located<Utf8PathBuf>>,
}

#[derive(Clone, Debug, Default, Deserialize)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct Fixpoint {
    /// Timeout in seconds for each fixpoint query (`-Ffixpoint-timeout`).
    pub timeout: Option<u64>,
}

#[derive(Clone, Debug, Default, Deserialize)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct Diagnostics {
    /// Produce more detailed error messages (`-Fflux-verbose`).
    pub verbose: Option<bool>,
    /// Emit suggestions in diagnostics (the inverse of `-Fno-suggestions`).
    pub suggestions: Option<bool>,
    /// Attach a note to failing items with a command to re-run them (`-Frerun-hint`).
    pub rerun_hint: Option<bool>,
}

#[derive(Clone, Debug, Default, Deserialize)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct Stats {
    /// Print a summary of the number of functions checked, trusted, etc. (`-Fsummary`).
    pub summary: Option<bool>,
    /// Print the time taken to analyze each function (`-Ftimings`).
    pub timings: Option<bool>,
    /// Compute statistics about annotations (`-Fannots`).
    pub annots: Option<bool>,
}

#[derive(Clone, Debug, Default, Deserialize)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct Debug {
    /// Directory where debug data is dumped (`-Flog-dir`).
    pub log_dir: Option<Located<Utf8PathBuf>>,
    pub dump_constraint: Option<bool>,
    pub dump_fhir: Option<bool>,
    pub dump_rty: Option<bool>,
    pub dump_checker_trace: Option<TraceLevel>,
    pub catch_bugs: Option<bool>,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TraceLevel {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

impl TraceLevel {
    fn as_str(self) -> &'static str {
        match self {
            TraceLevel::Error => "error",
            TraceLevel::Warn => "warn",
            TraceLevel::Info => "info",
            TraceLevel::Debug => "debug",
            TraceLevel::Trace => "trace",
        }
    }
}

impl Settings {
    /// Translates the settings into flags for the driver.
    pub fn to_flags(&self, target_dir: &Utf8Path) -> Vec<String> {
        let mut flags = vec![];
        if let Some(true) = self.cache.enabled {
            let dir = self
                .cache
                .dir
                .as_ref()
                .map(Located::resolve)
                .unwrap_or_else(|| target_dir.join("flux-cache"));
            flags.push(format!("-Fcache={dir}"));
        }
        if let Some(v) = self.fixpoint.timeout {
            flags.push(format!("-Ffixpoint-timeout={v}"));
        }
        if let Some(v) = self.diagnostics.verbose {
            flags.push(format!("-Fflux-verbose={v}"));
        }
        if let Some(v) = self.diagnostics.suggestions {
            flags.push(format!("-Fno-suggestions={}", !v));
        }
        if let Some(v) = self.diagnostics.rerun_hint {
            flags.push(format!("-Frerun-hint={v}"));
        }
        if let Some(v) = self.stats.summary {
            flags.push(format!("-Fsummary={v}"));
        }
        if let Some(v) = self.stats.timings {
            flags.push(format!("-Ftimings={v}"));
        }
        if let Some(v) = self.stats.annots {
            flags.push(format!("-Fannots={v}"));
        }
        if let Some(v) = &self.debug.log_dir {
            flags.push(format!("-Flog-dir={}", v.resolve()));
        }
        if let Some(v) = self.debug.dump_constraint {
            flags.push(format!("-Fdump-constraint={v}"));
        }
        if let Some(v) = self.debug.dump_fhir {
            flags.push(format!("-Fdump-fhir={v}"));
        }
        if let Some(v) = self.debug.dump_rty {
            flags.push(format!("-Fdump-rty={v}"));
        }
        if let Some(v) = self.debug.dump_checker_trace {
            flags.push(format!("-Fdump-checker-trace={}", v.as_str()));
        }
        if let Some(v) = self.debug.catch_bugs {
            flags.push(format!("-Fcatch-bugs={v}"));
        }
        flags
    }
}

impl FluxConfig {
    /// Discovers and loads the configuration for an invocation in the current directory.
    pub fn load() -> anyhow::Result<FluxConfig> {
        let cwd = Utf8PathBuf::try_from(env::current_dir()?)?;
        let flux_home = Utf8PathBuf::try_from(flux_home_dir())?;
        Self::load_files(&discover(&cwd, &flux_home))
    }

    /// Loads and merges the given files, ordered from highest to lowest precedence.
    fn load_files(paths: &[Utf8PathBuf]) -> anyhow::Result<FluxConfig> {
        let values = paths
            .iter()
            .rev()
            .map(|path| read_file(path))
            .collect::<anyhow::Result<Vec<_>>>()?;
        match ConfigValue::merge_all(values)? {
            Some(merged) => Self::from_value(merged),
            None => Ok(FluxConfig::default()),
        }
    }

    fn from_value(value: ConfigValue) -> anyhow::Result<FluxConfig> {
        Ok(FluxConfig { settings: value.deserialize_into()? })
    }
}

/// Returns the configuration files that apply to `cwd`, ordered from highest to lowest
/// precedence.
fn discover(cwd: &Utf8Path, flux_home: &Utf8Path) -> Vec<Utf8PathBuf> {
    let mut paths: Vec<Utf8PathBuf> = cwd
        .ancestors()
        .map(|dir| dir.join(".flux").join("config.toml"))
        .filter(|path| path.is_file())
        .collect();
    let home_config = flux_home.join("config.toml");
    if home_config.is_file() && !paths.iter().any(|path| same_file(path, &home_config)) {
        paths.push(home_config);
    }
    paths
}

fn same_file(a: &Utf8Path, b: &Utf8Path) -> bool {
    match (fs::canonicalize(a), fs::canonicalize(b)) {
        (Ok(a), Ok(b)) => a == b,
        _ => a == b,
    }
}

/// Reads a configuration file and validates it on its own, so invalid values are reported even if
/// another file overrides them.
fn read_file(path: &Utf8Path) -> anyhow::Result<ConfigValue> {
    let value = ConfigValue::parse_file(path)?;
    FluxConfig::from_value(value.clone())?;
    Ok(value)
}
