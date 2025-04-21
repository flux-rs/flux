use std::{env, path::PathBuf, process, sync::LazyLock};

use serde::Deserialize;
pub use toml::Value;

use crate::{PointerWidth, SmtSolver};

const FLUX_FLAG_PREFIX: &str = "-F";

/// Exit status code used for invalid flags.
pub const EXIT_FAILURE: i32 = 2;

pub struct Flags {
    /// Sets the directory where constraints, timing and cache are saved. Defaults to `./log/`.
    pub log_dir: PathBuf,
    /// Dump constraints generated for each function (debugging)
    pub dump_constraint: bool,
    /// Saves the checker's trace (debugging)
    pub dump_checker_trace: bool,
    /// Saves the `fhir` for each item (debugging)
    pub dump_fhir: bool,
    /// Saves the the `fhir` (debugging)
    pub dump_rty: bool,
    /// Saves the low-level MIR for each analyzed function (debugging)
    pub dump_mir: bool,
    /// Saves the low-level MIR for each analyzed function (debugging)
    pub catch_bugs: bool,
    /// Only checks definitions containing `name` as a substring
    pub check_def: String,
    /// Only checks the specified files. Takes a list of comma separated paths
    pub check_files: Paths,
    /// Set the pointer size (either `32` or `64`), used to determine if an integer cast is lossy
    /// (default `64`).
    pub pointer_width: PointerWidth,
    /// If present switches on query caching and saves the cache in the provided path
    pub cache: Option<PathBuf>,
    pub verbose: bool,
    /// Compute statistics about number and size of annotations. Dumps file to [`Self.log_dir`]
    pub annots: bool,
    /// Print statistics about time taked to analyze each fuction. Also dumps a file with the raw
    /// times for each function.
    pub timings: bool,
    /// Default solver. Either `z3` or `cvc5`.
    pub solver: SmtSolver,
    /// Enables qualifier scrapping in fixpoint
    pub scrape_quals: bool,
    /// Translates _monomorphic_ `defs` functions into SMT `define-fun` instead of inlining them
    /// away inside `flux`.
    pub smt_define_fun: bool,
    /// If true checks for over and underflow on arithmetic integer operations, default `false`. When
    /// set to `false`, it still checks for underflow on unsigned integer subtraction.
    pub check_overflow: bool,
}

impl Default for Flags {
    fn default() -> Self {
        Self {
            log_dir: PathBuf::from("./log/"),
            dump_constraint: false,
            dump_checker_trace: false,
            dump_fhir: false,
            dump_rty: false,
            dump_mir: false,
            catch_bugs: false,
            pointer_width: PointerWidth::default(),
            check_def: String::new(),
            check_files: Paths::default(),
            cache: None,
            check_overflow: false,
            scrape_quals: false,
            solver: SmtSolver::default(),
            smt_define_fun: false,
            verbose: false,
            annots: false,
            timings: false,
        }
    }
}

pub(crate) static FLAGS: LazyLock<Flags> = LazyLock::new(|| {
    let mut flags = Flags::default();
    for arg in env::args() {
        let Some((key, value)) = parse_flux_arg(&arg) else { continue };

        let result = match key {
            "log-dir" => parse_path_buf(&mut flags.log_dir, value),
            "dump-constraint" => parse_bool(&mut flags.dump_constraint, value),
            "dump-checker-trace" => parse_bool(&mut flags.dump_checker_trace, value),
            "dump-mir" => parse_bool(&mut flags.dump_mir, value),
            "dump-fhir" => parse_bool(&mut flags.dump_fhir, value),
            "dump-rty" => parse_bool(&mut flags.dump_rty, value),
            "catch-bugs" => parse_bool(&mut flags.catch_bugs, value),
            "pointer-width" => parse_pointer_width(&mut flags.pointer_width, value),
            "check-overflow" => parse_bool(&mut flags.check_overflow, value),
            "scrape-quals" => parse_bool(&mut flags.scrape_quals, value),
            "solver" => parse_solver(&mut flags.solver, value),
            "verbose" => parse_bool(&mut flags.verbose, value),
            "smt-define-fun" => parse_bool(&mut flags.smt_define_fun, value),
            "annots" => parse_bool(&mut flags.annots, value),
            "timings" => parse_bool(&mut flags.timings, value),
            "cache" => parse_opt_path_buf(&mut flags.cache, value),
            "check-def" => parse_string(&mut flags.check_def, value),
            "check-files" => parse_check_files(&mut flags.check_files, value),
            _ => {
                eprintln!("error: unknown flux option: `{key}`");
                process::exit(EXIT_FAILURE);
            }
        };
        if let Err(reason) = result {
            eprintln!("error: incorrect value for flux option `{key}` - `{reason}`");
            process::exit(1);
        }
    }
    flags
});

#[derive(Default)]
pub struct Paths {
    paths: Option<Vec<PathBuf>>,
}

impl Paths {
    pub fn is_checked_file(&self, file: &str) -> bool {
        self.paths
            .as_ref()
            .is_none_or(|p| p.iter().any(|p| p.to_str().unwrap() == file))
    }
}

impl<'de> Deserialize<'de> for Paths {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let paths: Vec<PathBuf> = String::deserialize(deserializer)?
            .split(",")
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(PathBuf::from)
            .collect();

        let paths = if paths.is_empty() { None } else { Some(paths) };

        Ok(Paths { paths })
    }
}

pub fn is_flux_arg(arg: &str) -> bool {
    parse_flux_arg(arg).is_some()
}

fn parse_flux_arg(arg: &str) -> Option<(&str, Option<&str>)> {
    let arg = arg.strip_prefix(FLUX_FLAG_PREFIX)?;
    if arg.is_empty() {
        return None;
    }
    if let Some((k, v)) = arg.split_once('=') { Some((k, Some(v))) } else { Some((arg, None)) }
}

fn parse_bool(slot: &mut bool, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some("y") | Some("yes") | Some("on") | Some("true") | None => {
            *slot = true;
            Ok(())
        }
        Some("n") | Some("no") | Some("off") | Some("false") => {
            *slot = false;
            Ok(())
        }
        _ => {
            Err(
                "expected no value or one of `y`, `yes`, `on`, `true`, `n`, `no`, `off`, or `false`",
            )
        }
    }
}

fn parse_path_buf(slot: &mut PathBuf, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = PathBuf::from(s);
            Ok(())
        }
        None => Err("a path"),
    }
}

fn parse_pointer_width(slot: &mut PointerWidth, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = s.parse()?;
            Ok(())
        }
        _ => Err(PointerWidth::ERROR),
    }
}

fn parse_solver(slot: &mut SmtSolver, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = s.parse()?;
            Ok(())
        }
        _ => Err(SmtSolver::ERROR),
    }
}

fn parse_opt_path_buf(slot: &mut Option<PathBuf>, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = Some(PathBuf::from(s));
            Ok(())
        }
        None => Err("a path"),
    }
}

fn parse_string(slot: &mut String, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            *slot = s.to_string();
            Ok(())
        }
        None => Err("a string"),
    }
}

fn parse_check_files(slot: &mut Paths, v: Option<&str>) -> Result<(), &'static str> {
    match v {
        Some(s) => {
            let paths: Vec<PathBuf> = s
                .split(",")
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(PathBuf::from)
                .collect();
            *slot = Paths { paths: if paths.is_empty() { None } else { Some(paths) } };
            Ok(())
        }
        None => Err("a comma separated list of paths"),
    }
}
