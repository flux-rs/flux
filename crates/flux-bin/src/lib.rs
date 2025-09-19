use cargo_metadata::camino::Utf8Path;
use flux_config::{OverflowMode, SmtSolver};
use serde::Deserialize;

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
}

impl FluxMetadata {
    pub fn into_flags(self, target_dir: &Utf8Path, glob_prefix: Option<&Utf8Path>) -> Vec<String> {
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
        if let Some(v) = self.scrape_quals {
            flags.push(format!("-Fscrape-quals={v}"));
        }
        if let Some(v) = self.smt_define_fun {
            flags.push(format!("-Fsmt-define-fun={v}"));
        }
        if let Some(v) = self.default_trusted {
            flags.push(format!("-Ftrusted={v}"));
        }
        if let Some(v) = self.default_ignore {
            flags.push(format!("-Fignore={v}"));
        }
        if let Some(v) = self.allow_uninterpreted_cast {
            flags.push(format!("-Fallow-uninterpreted-cast={v}"));
        }
        if let Some(patterns) = self.include {
            for pat in patterns {
                if let Some(glob_prefix) = glob_prefix
                    && !glob_prefix.as_str().is_empty()
                {
                    // I haven't tested this on windows, but it should work because `globset`
                    // will normalize patterns to use `/` as separator
                    // don't use the empty `glob_prefix` as that makes the pattern hang off root!
                    flags.push(format!("-Finclude={glob_prefix}/{pat}"));
                } else {
                    flags.push(format!("-Finclude={pat}"));
                }
            }
        }
        flags
    }
}
