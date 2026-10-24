use anyhow::Context;
use cargo_metadata::{Package, camino::Utf8Path};
use flux_config::{LeanMode, OverflowMode, RawDerefMode, SmtSolver, UifOps};
use serde::Deserialize;

pub mod cargo_flux_opts;
pub mod cargo_style;
pub mod config;
pub mod utils;

/// The `[package.metadata.flux]` table in `Cargo.toml`.
///
/// The table describes properties of the crate, e.g., which files are verified and under which
/// semantics. Settings controlling how Flux runs belong in `.flux/config.toml` (see [`config`]).
#[derive(Deserialize, Debug, Default)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct FluxMetadata {
    /// Whether the package is checked by Flux
    pub enabled: bool,
    /// If present, only check files that match any of the glob patterns. Patterns are checked
    /// relative to the location of the manifest file.
    pub include: Option<Vec<String>>,
    /// Overflow checking mode
    pub check_overflow: Option<OverflowMode>,
    /// If present, every function in the crate is implicitly labeled with a `no_panic` by default.
    /// This means that the only way a function can panic is if it calls an external function
    /// without this attribute.
    pub no_panic: Option<bool>,
    /// Enable uninterpreted casts
    pub allow_uninterpreted_cast: Option<bool>,
    /// Whether to allow raw pointer dereferences
    pub allow_raw_deref: Option<RawDerefMode>,
    /// Lean mode
    pub lean: Option<LeanMode>,
    /// The solver used to verify the crate
    pub solver: Option<SmtSolver>,
    /// Enable qualifier scrapping in fixpoint
    pub scrape_quals: Option<bool>,
    /// Binary operators to encode as uninterpreted functions
    pub uif_ops: Option<UifOps>,
    pub trusted: Trusted,
    pub trusted_impl: TrustedImpl,
    pub ignore: Ignore,
}

/// The `[package.metadata.flux.trusted]` table.
#[derive(Deserialize, Debug, Default)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct Trusted {
    /// Whether items are trusted by default
    pub default: Option<bool>,
    /// If present, only consider `DefId` in files that match any of the glob patterns as trusted.
    /// Patterns are checked relative to the location of the manifest file.
    pub files: Option<Vec<String>>,
}

/// The `[package.metadata.flux.trusted-impl]` table.
#[derive(Deserialize, Debug, Default)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct TrustedImpl {
    /// If present, only consider `DefId` in files that match any of the glob patterns as
    /// trusted_impl. Patterns are checked relative to the location of the manifest file.
    pub files: Option<Vec<String>>,
}

/// The `[package.metadata.flux.ignore]` table.
#[derive(Deserialize, Debug, Default)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct Ignore {
    /// Whether items are ignored by default
    pub default: Option<bool>,
}

impl FluxMetadata {
    /// Reads the `[package.metadata.flux]` table of `package`.
    pub fn from_package(package: &Package) -> anyhow::Result<FluxMetadata> {
        let Some(value) = package.metadata.get("flux") else { return Ok(Self::default()) };
        let context =
            || format!("invalid `[package.metadata.flux]` in `{}`", package.manifest_path);
        serde_json::from_value(value.clone()).with_context(context)
    }

    pub fn into_flags(
        self,
        include_pattern_prefix: Option<&Utf8Path>,
        only_check: Option<&str>,
    ) -> Vec<String> {
        let mut flags = vec![];
        if let Some(v) = self.solver {
            flags.push(format!("-Fsolver={v}"));
        }
        if let Some(v) = self.check_overflow {
            flags.push(format!("-Fcheck-overflow={v}"));
        }
        if let Some(v) = self.uif_ops {
            flags.push(format!("-Fuif-ops={v}"));
        }
        if let Some(v) = self.lean {
            flags.push(format!("-Flean={v}"));
        }
        if let Some(v) = self.scrape_quals {
            flags.push(format!("-Fscrape-quals={v}"));
        }
        if let Some(v) = self.trusted.default {
            flags.push(format!("-Ftrusted={v}"));
        }
        if let Some(v) = self.no_panic {
            flags.push(format!("-Fno-panic={v}"));
        }
        if let Some(v) = self.ignore.default {
            flags.push(format!("-Fignore={v}"));
        }
        if let Some(v) = self.allow_uninterpreted_cast {
            flags.push(format!("-Fallow-uninterpreted-cast={v}"));
        }
        if let Some(v) = self.allow_raw_deref {
            flags.push(format!("-Fallow-raw-deref={v}"));
        }
        if let Some(only_check) = only_check {
            flags.push(format!("-Finclude={only_check}"));
        } else if let Some(patterns) = self.include {
            for pat in patterns {
                if let Some(prefix) = include_pattern_prefix {
                    flags.push(format!("-Finclude={}", prepend_prefix_to_pattern(prefix, &pat)));
                } else {
                    flags.push(format!("-Finclude={pat}"));
                }
            }
        }
        if let Some(patterns) = self.trusted.files {
            for pat in patterns {
                if let Some(glob_prefix) = include_pattern_prefix
                    && !glob_prefix.as_str().is_empty()
                {
                    flags.push(format!("-Finclude-trusted={glob_prefix}/{pat}"));
                } else {
                    flags.push(format!("-Finclude-trusted={pat}"));
                }
            }
        }
        if let Some(patterns) = self.trusted_impl.files {
            for pat in patterns {
                if let Some(glob_prefix) = include_pattern_prefix
                    && !glob_prefix.as_str().is_empty()
                {
                    flags.push(format!("-Finclude-trusted-impl={glob_prefix}/{pat}"));
                } else {
                    flags.push(format!("-Finclude-trusted-impl={pat}"));
                }
            }
        }
        flags
    }
}

fn prepend_prefix_to_pattern(prefix: &Utf8Path, pat: &str) -> String {
    // don't use the empty `prefix` as that makes the pattern hang off root!
    if prefix.as_str().is_empty() {
        return pat.to_string();
    }
    if pat.starts_with("def:") {
        return pat.to_string();
    }
    // I haven't tested this on windows, but it should work because `globset`
    // will normalize patterns to use `/` as separator.
    if let Some(pat) = pat.strip_prefix("glob:") {
        format!("glob:{prefix}/{pat}")
    } else if let Some(pat) = pat.strip_prefix("span:") {
        // span patterns are of the form `span:<file>:<line>:<column>""
        format!("span:{prefix}/{pat}")
    } else {
        // no prefix defaults to glob patterns.
        format!("{prefix}/{pat}")
    }
}
