use cargo_metadata::camino::Utf8Path;
use flux_config::SmtSolver;
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
    pub check_overflow: Option<bool>,
    /// Enable overflow checking
    pub smt_define_fun: Option<bool>,
    /// Set trusted trusted
    pub default_trusted: Option<bool>,
    /// Set trusted ignore
    pub default_ignore: Option<bool>,
}

impl FluxMetadata {
    pub fn into_flags(self, target_dir: &Utf8Path) -> Vec<String> {
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
        flags
    }
}
