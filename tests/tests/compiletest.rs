#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::{env, path::PathBuf, str::FromStr};

use compiletest_rs::{Config, common::Mode};
use flux_dev::{Suite, default_flags};
use flux_sysroot::SysrootManifest;
use itertools::Itertools;

#[derive(Debug)]
struct Args {
    filters: Vec<String>,
    flux_driver: PathBuf,
    sysroot: PathBuf,
    /// Which subset of test suites to run.
    suite: Suite,
    /// Timeout in seconds for each fixpoint query.
    fixpoint_timeout: Option<u64>,
}

impl Args {
    fn parse() -> Args {
        let mut filters = vec![];
        let mut sysroot = None;
        let mut flux_driver = None;
        let mut suite = None;
        let mut fixpoint_timeout = None;
        for (arg, val) in env::args().tuple_windows() {
            match &arg[..] {
                "--filter" => filters.push(val.clone()),
                "--flux-driver" => {
                    if flux_driver.is_some() {
                        panic!("option '--flux-driver' given more than once");
                    }
                    flux_driver = Some(val.clone());
                }
                "--sysroot" => {
                    if sysroot.is_some() {
                        panic!("option '--sysroot' given more than once");
                    }
                    sysroot = Some(val.clone());
                }
                "--suite" => {
                    if suite.is_some() {
                        panic!("option '--suite' given more than once");
                    }
                    suite = Some(
                        Suite::from_str(&val)
                            .unwrap_or_else(|e| panic!("invalid --suite value `{val}`: {e}")),
                    );
                }
                "--fixpoint-timeout" => {
                    if fixpoint_timeout.is_some() {
                        panic!("option '--fixpoint-timeout' given more than once");
                    }
                    fixpoint_timeout = Some(val.parse().unwrap_or_else(|e| {
                        panic!("invalid --fixpoint-timeout value `{val}`: {e}")
                    }));
                }
                _ => {}
            }
        }
        let Some(flux_driver) = flux_driver else {
            panic!("option '--flux-driver' must be provided");
        };
        let Some(sysroot) = sysroot else {
            panic!("option '--sysroot' must be provided");
        };
        let Some(suite) = suite else {
            panic!("option '--suite' must be provided");
        };
        Args {
            filters,
            flux_driver: PathBuf::from(flux_driver),
            sysroot: PathBuf::from(sysroot),
            suite,
            fixpoint_timeout,
        }
    }
}

fn test_runner(_: &[&()]) {
    let args = Args::parse();
    let mut config =
        Config { rustc_path: args.flux_driver, filters: args.filters, ..Config::default() };

    let mut flags = default_flags(&args.sysroot, SysrootManifest::extern_args(&args.sysroot));

    // Pass `--emit=metadata` and `-Ffull-compilation=on` to make sure we emit `.fluxmeta` and
    // other artifacts for tests using `@aux-build`.
    flags.extend(["--emit=metadata".to_string(), "-Ffull-compilation=on".to_string()]);

    // Pass `-Fsummary=off` to disable printing the summary at the end of each test
    flags.extend(["-Fsummary=off".to_string()]);

    if let Some(timeout) = args.fixpoint_timeout {
        flags.push(format!("-Ffixpoint-timeout={timeout}"));
    }

    config.target_rustcflags = Some(flags.join(" "));

    config.clean_rmeta();
    config.clean_rlib();
    config.strict_headers = true;

    let path = args.suite.pos_tests();
    if path.exists() {
        config.mode = Mode::Ui;
        config.src_base = path;
        compiletest_rs::run_tests(&config);
    }

    let path = args.suite.neg_tests();
    if path.exists() {
        config.mode = Mode::CompileFail;
        config.src_base = path;
        compiletest_rs::run_tests(&config);
        check_signature_suggestions(&config, &config.src_base);
    }
}

/// Compile-fail mode checks errors, but does not apply rustfix suggestions. Opted-in
/// tests also check the edits themselves and verify the resulting Flux contracts.
fn check_signature_suggestions(config: &Config, dir: &std::path::Path) {
    use std::{collections::HashSet, fs, process::Command};

    use rustfix::{Filter, apply_suggestions, get_suggestions_from_json};

    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            check_signature_suggestions(config, &path);
            continue;
        }
        if path.extension().is_none_or(|ext| ext != "rs")
            || (!config.filters.is_empty()
                && !config
                    .filters
                    .iter()
                    .any(|filter| path.to_string_lossy().contains(filter)))
        {
            continue;
        }
        let source = fs::read_to_string(&path).unwrap();
        let Some(count) = source
            .lines()
            .find_map(|line| line.strip_prefix("// check-suggestions: "))
        else {
            continue;
        };
        let count: usize = count.parse().unwrap();
        let temp = tempfile::tempdir().unwrap();
        let compile = |input: &std::path::Path| {
            let mut cmd = Command::new(&config.rustc_path);
            cmd.args(
                config
                    .target_rustcflags
                    .as_deref()
                    .unwrap()
                    .split_whitespace(),
            );
            for line in source.lines() {
                if let Some(flags) = line.strip_prefix("// compile-flags: ") {
                    cmd.args(flags.split_whitespace());
                }
            }
            cmd.args(["--error-format=json", "--crate-name=suggestion_test", "-Aunused"])
                .arg("--out-dir")
                .arg(temp.path())
                .arg(input)
                .output()
                .unwrap()
        };
        let output = compile(&path);
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(!output.status.success(), "{}: expected errors", path.display());
        let suggestions = get_suggestions_from_json(
            &stderr,
            &HashSet::<String>::new(),
            Filter::MachineApplicableOnly,
        )
        .unwrap();
        assert_eq!(suggestions.len(), count, "{}: {stderr}", path.display());
        let replacements = suggestions
            .iter()
            .flat_map(|s| &s.solutions)
            .flat_map(|s| &s.replacements)
            .map(|r| r.replacement.as_str())
            .collect::<Vec<_>>()
            .join("\n");
        for expected in source
            .lines()
            .filter_map(|line| line.strip_prefix("// suggestion: "))
        {
            assert!(
                replacements.contains(expected),
                "{}: missing `{expected}` in {replacements}",
                path.display()
            );
        }
        let mut fixed = apply_suggestions(&source, &suggestions).unwrap();
        // Auxiliary modules must still resolve relative to the original input.
        for line in source.lines() {
            if let Some(relative) = line
                .strip_prefix("#[path = \"")
                .and_then(|s| s.strip_suffix("\"]"))
            {
                let absolute = path
                    .parent()
                    .unwrap()
                    .join(relative)
                    .canonicalize()
                    .unwrap();
                fixed = fixed.replace(line, &format!("#[path = {:?}]", absolute));
            }
        }
        let fixed_path = temp.path().join("fixed.rs");
        // Enable callers that witness satisfiability/preservation of the suggested contract.
        fs::write(&fixed_path, fixed.replace("#[cfg(flux_test_suggestions_applied)]", "")).unwrap();
        let output = compile(&fixed_path);
        assert!(
            output.status.success(),
            "{}: suggested contracts failed:\n{}",
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        println!("signature suggestions: {} ... ok", path.display());
    }
}
