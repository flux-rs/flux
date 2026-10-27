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
//! Settings can be overridden for specific packages in `[package.<spec>]` tables, where `<spec>`
//! is a package name, `<name>@<version>`, or `*` for all packages that are not workspace members.
//! As in cargo's profile overrides, a package's settings are taken from its own table, then from
//! `[package."*"]`, and then from the top level.
//!

mod value;

use std::{collections::BTreeMap, env, fs};

use anyhow::{Context, bail};
use cargo_metadata::camino::{Utf8Path, Utf8PathBuf};
use flux_sysroot::flux_home_dir;
use serde::Deserialize;
use value::ConfigValue;
pub use value::{Located, Location};

/// The merged content of all configuration files.
#[derive(Debug, Default)]
pub struct FluxConfig {
    pub build: Build,
    /// Top-level settings, kept untyped to merge them with package overrides. `None` if there are
    /// no configuration files.
    settings: Option<ConfigValue>,
    /// `[package.<spec>]` tables, indexed by spec.
    packages: BTreeMap<String, PackageOverride>,
}

/// A `[package.<spec>]` table.
#[derive(Debug)]
struct PackageOverride {
    settings: ConfigValue,
    fluxflags: Option<Vec<String>>,
}

/// The configuration of a single package.
#[derive(Debug)]
pub struct PackageConfig {
    pub settings: Settings,
    /// Flags from the package overrides. They are passed before the global flags, like cargo does
    /// with `rustflags` in profile overrides.
    pub fluxflags: Vec<String>,
}

/// The `[build]` table.
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct Build {
    /// Extra flags passed to every package checked by Flux, like cargo's `build.rustflags`.
    pub fluxflags: Option<StringList>,
}

/// A list of strings written either as an array or as a space-separated string.
#[derive(Clone, Debug, Deserialize)]
#[serde(untagged)]
pub enum StringList {
    String(String),
    List(Vec<String>),
}

impl StringList {
    fn into_vec(self) -> Vec<String> {
        match self {
            StringList::String(s) => split_space_separated(&s),
            StringList::List(list) => list,
        }
    }
}

/// Environment variable with flags separated by `0x1f` (ASCII Unit Separator). Takes precedence
/// over [`FLUXFLAGS`]. Like cargo's `CARGO_ENCODED_RUSTFLAGS`, it allows flags containing spaces.
pub const FLUX_ENCODED_FLAGS: &str = "FLUX_ENCODED_FLAGS";

/// Environment variable with space-separated flags. Takes precedence over `build.fluxflags`.
pub const FLUXFLAGS: &str = "FLUXFLAGS";

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

/// Top-level keys that are not [`Settings`].
const BUILD_KEY: &str = "build";
const PACKAGE_KEY: &str = "package";

/// Key for flags in a `[package.<spec>]` table.
const FLUXFLAGS_KEY: &str = "fluxflags";

/// Spec matching all packages that are not workspace members.
const ALL_NON_MEMBERS: &str = "*";

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

    fn from_value(mut value: ConfigValue) -> anyhow::Result<FluxConfig> {
        let build: Build = match value.remove(BUILD_KEY) {
            Some(build) => {
                build
                    .deserialize_into()
                    .context("invalid `[build]` table")?
            }
            None => Build::default(),
        };
        let packages = match value.remove(PACKAGE_KEY) {
            Some(packages) => {
                let ConfigValue::Table(packages, _) = packages else {
                    bail!("{}: `package` must be a table", packages.location());
                };
                packages
                    .into_iter()
                    .map(|(spec, value)| {
                        let package = PackageOverride::from_value(value)
                            .with_context(|| format!("invalid `[package.\"{spec}\"]` table"))?;
                        Ok((spec, package))
                    })
                    .collect::<anyhow::Result<_>>()?
            }
            None => BTreeMap::new(),
        };
        value.clone().deserialize_into::<Settings>()?;
        Ok(FluxConfig { build, settings: Some(value), packages })
    }

    /// Returns the configuration for the package `name` at `version`.
    pub fn for_package(
        &self,
        name: &str,
        version: &str,
        is_workspace_member: bool,
    ) -> anyhow::Result<PackageConfig> {
        let matching: Vec<_> = self
            .packages
            .iter()
            .filter(|(spec, _)| spec_matches(spec, name, version))
            .collect();
        if matching.len() >= 2 {
            bail!(
                "multiple `[package]` tables in `.flux/config.toml` match package `{name}`: `{}` and \
                 `{}`",
                matching[0].0,
                matching[1].0
            );
        }
        let named = matching.first().map(|(_, package)| *package);
        let all_non_members =
            if is_workspace_member { None } else { self.packages.get(ALL_NON_MEMBERS) };

        // Overrides in increasing order of precedence. Settings are merged field by field.
        let mut settings: Vec<ConfigValue> = self.settings.iter().cloned().collect();
        let mut fluxflags = vec![];
        for package in [all_non_members, named].into_iter().flatten() {
            settings.push(package.settings.clone());
            if let Some(flags) = &package.fluxflags {
                fluxflags = flags.clone();
            }
        }
        let settings = match ConfigValue::merge_all(settings)? {
            Some(settings) => settings.deserialize_into()?,
            None => Settings::default(),
        };
        Ok(PackageConfig { settings, fluxflags })
    }

    /// Returns the specs of `[package.<spec>]` tables that match none of `packages`, given as pairs
    /// of name and version.
    pub fn unmatched_specs(&self, packages: &[(String, String)]) -> Vec<&str> {
        self.packages
            .keys()
            .filter(|spec| {
                *spec != ALL_NON_MEMBERS
                    && !packages
                        .iter()
                        .any(|(name, version)| spec_matches(spec, name, version))
            })
            .map(String::as_str)
            .collect()
    }

    /// Returns the extra flags passed to every package. Following cargo's rules for rustflags,
    /// they come from the first source that is set among [`FLUX_ENCODED_FLAGS`], [`FLUXFLAGS`] and
    /// `build.fluxflags`. Sources are not combined.
    pub fn global_fluxflags(&self) -> Vec<String> {
        if let Ok(flags) = env::var(FLUX_ENCODED_FLAGS) {
            if flags.is_empty() {
                vec![]
            } else {
                flags.split('\x1f').map(str::to_string).collect()
            }
        } else if let Ok(flags) = env::var(FLUXFLAGS) {
            split_space_separated(&flags)
        } else {
            self.build
                .fluxflags
                .clone()
                .map(StringList::into_vec)
                .unwrap_or_default()
        }
    }
}

impl PackageOverride {
    fn from_value(mut settings: ConfigValue) -> anyhow::Result<PackageOverride> {
        let fluxflags = match settings.remove(FLUXFLAGS_KEY) {
            Some(value) => Some(value.deserialize_into::<StringList>()?.into_vec()),
            None => None,
        };
        settings.clone().deserialize_into::<Settings>()?;
        Ok(PackageOverride { settings, fluxflags })
    }
}

/// Whether `spec` is `name` or `name@version`.
fn spec_matches(spec: &str, name: &str, version: &str) -> bool {
    match spec.split_once('@') {
        Some((spec_name, spec_version)) => spec_name == name && spec_version == version,
        None => spec == name,
    }
}

fn split_space_separated(s: &str) -> Vec<String> {
    s.split(' ')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect()
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
