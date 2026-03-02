use cargo_metadata::camino::Utf8Path;
use flux_config::{LeanMode, OverflowMode, SmtSolver};
use serde::Deserialize;

pub mod cargo_flux_opts;
pub mod cargo_style;
pub mod utils;

#[derive(Deserialize, Debug, Default)]
#[serde(default, deny_unknown_fields)]
pub struct FluxMetadata {
    pub enabled: bool,
    /// Enables fixpoint query caching. Saves cache in `target/FLUXCACHE`
    pub cache: Option<bool>,
    /// Set the default solver
    pub solver: Option<SmtSolver>,
    /// Enable qualifier scrapping in fixpoint
    pub scrape_quals: Option<bool>,
    /// Enable overflow checking
    pub check_overflow: Option<OverflowMode>,
    /// Enable uninterpreted casts
    pub allow_uninterpreted_cast: Option<bool>,
    /// Enable flux-defs to be defined as SMT functions
    pub smt_define_fun: Option<bool>,
    /// Set trusted to trusted
    pub default_trusted: Option<bool>,
    /// Set trusted to ignore
    pub default_ignore: Option<bool>,
    /// If present, only check files that match any of the glob patterns. Patterns are checked
    /// relative to the location of the manifest file.
    pub include: Option<Vec<String>>,
    /// If present, every function in the module is implicitly labeled with a `no_panic` by default.
    /// This means that the only way a function can panic is if it calls an external function without this attribute.
    pub no_panic: Option<bool>,
    /// If present, enables lean mode
    pub lean: Option<LeanMode>,
    /// If present, dumps the fixpoint constraint to a file
    pub dump_constraint: Option<bool>,
}

impl FluxMetadata {
    pub fn into_flags(
        self,
        target_dir: &Utf8Path,
        inlude_pattern_prefix: Option<&Utf8Path>,
    ) -> Vec<String> {
        let mut flags = vec![];
        if let Some(true) = self.cache {
            flags.push(format!("-Fcache={}", target_dir.join("FLUXCACHE")));
        }
        if let Some(v) = self.solver {
            flags.push(format!("-Fsolver={v}"));
        }
        if let Some(v) = self.check_overflow {
            flags.push(format!("-Fcheck-overflow={v}"));
        }
        if let Some(v) = self.lean {
            flags.push(format!("-Flean={v}"));
        }
        if let Some(v) = self.dump_constraint {
            flags.push(format!("-Fdump-constraint={v}"));
        }
        if let Some(v) = self.scrape_quals {
            flags.push(format!("-Fscrape-quals={v}"));
        }
        if let Some(v) = self.smt_define_fun {
            flags.push(format!("-Fsmt-define-fun={v}"));
        }
        if let Some(v) = self.default_trusted {
            flags.push(format!("-Ftrusted={v}"));
        }
        if let Some(v) = self.no_panic {
            flags.push(format!("-Fno-panic={v}"));
        }
        if let Some(v) = self.default_ignore {
            flags.push(format!("-Fignore={v}"));
        }
        if let Some(v) = self.allow_uninterpreted_cast {
            flags.push(format!("-Fallow-uninterpreted-cast={v}"));
        }
        if let Some(patterns) = self.include {
            for pat in patterns {
                if let Some(prefix) = inlude_pattern_prefix {
                    flags.push(format!("-Finclude={}", prepend_prefix_to_pattern(prefix, &pat)));
                } else {
                    flags.push(format!("-Finclude={pat}"));
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
