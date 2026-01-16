#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::{env, fs, path::PathBuf};

use compiletest_rs::{Config, common::Mode};
use itertools::Itertools;
use tests::{FLUX_SYSROOT, default_flags};
use walkdir::WalkDir;

#[derive(Debug)]
struct Args {
    filters: Vec<String>,
    flux: PathBuf,
    sysroot: PathBuf,
    emit_lean: bool,
}

impl Args {
    fn parse() -> Args {
        let mut filters = vec![];
        let mut sysroot = None;
        let mut flux = None;
        let mut emit_lean = false;
        for (arg, val) in env::args().tuple_windows() {
            match &arg[..] {
                "--filter" => {
                    filters.push(val);
                }
                "--flux" => {
                    if flux.is_some() {
                        panic!("option '--flux' given more than once");
                    }
                    flux = Some(val);
                }
                "--sysroot" => {
                    if sysroot.is_some() {
                        panic!("option '--sysroot' given more than once");
                    }
                    sysroot = Some(val);
                }
                "--emit-lean" => {
                    emit_lean = true;
                }
                _ => {}
            }
        }
        // Also check for --emit-lean as a standalone arg (not followed by a value)
        if env::args().any(|a| a == "--emit-lean") {
            emit_lean = true;
        }
        let Some(flux) = flux else {
            panic!("option '--flux' must be provided");
        };
        let Some(sysroot) = sysroot else {
            panic!("option '--sysroot' must be provided");
        };
        Args { filters, flux: PathBuf::from(flux), sysroot: PathBuf::from(sysroot), emit_lean }
    }
}

fn test_runner(_: &[&()]) {
    let args = Args::parse();
    let mut config = Config { rustc_path: args.flux, filters: args.filters, ..Config::default() };

    let mut flags = default_flags();

    // Pass `--emit=metadata` and `-Ffull-compilation=on` to make sure we emit `.fluxmeta` and
    // other artifacts for tests using `@aux-build`.
    flags.extend(["--emit=metadata".to_string(), "-Ffull-compilation=on".to_string()]);

    // Pass `-Fsummary=off` to disable printing the summary at the end of each test
    flags.extend(["-Fsummary=off".to_string()]);

    config.target_rustcflags = Some(flags.join(" "));

    config.clean_rmeta();
    config.clean_rlib();
    config.strict_headers = true;

    // SAFETY: this is safe because this part of the code is single threaded
    unsafe {
        // Set the sysroot dir so the `flux` binary can find the correct `flux-driver.
        env::set_var(FLUX_SYSROOT, args.sysroot);
    }

    let path: PathBuf = ["tests", "pos"].iter().collect();
    if path.exists() {
        if args.emit_lean {
            run_tests_with_lean_emit(&config, &path);
        } else {
            config.mode = Mode::Ui;
            config.src_base = path;
            compiletest_rs::run_tests(&config);
        }
    }

    let path: PathBuf = ["tests", "neg"].iter().collect();
    if path.exists() && !args.emit_lean {
        config.mode = Mode::CompileFail;
        config.src_base = path;
        compiletest_rs::run_tests(&config);
    }
}

/// Run tests in `tests/pos/` with `-Flean=emit`, placing lean output in `./lean_bench/<path>/<to>/<file>/`
fn run_tests_with_lean_emit(base_config: &Config, pos_path: &PathBuf) {
    use std::panic;

    let lean_bench_dir = PathBuf::from("lean_bench");
    let mut failures: Vec<PathBuf> = Vec::new();
    let mut total_tests = 0;

    for entry in WalkDir::new(pos_path)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "rs"))
    {
        total_tests += 1;
        let test_path = entry.path().to_path_buf();

        // Get the relative path from tests/pos/ (e.g., "surface/test00.rs")
        let rel_path = test_path.strip_prefix(pos_path).unwrap();

        // Create lean output dir: ./lean_bench/<path>/<to>/<file>/
        // e.g., for tests/pos/surface/test00.rs -> ./lean_bench/surface/test00/
        let mut lean_dir = lean_bench_dir.clone();
        if let Some(parent) = rel_path.parent() {
            lean_dir.push(parent);
        }
        if let Some(stem) = rel_path.file_stem() {
            lean_dir.push(stem);
        }

        // Create the directory if it doesn't exist
        if let Err(e) = fs::create_dir_all(&lean_dir) {
            eprintln!("Failed to create directory {:?}: {}", lean_dir, e);
            failures.push(test_path.clone());
            continue;
        }

        // Create a config for this specific test with lean flags
        let mut test_config = base_config.clone();
        test_config.mode = Mode::Ui;
        test_config.src_base = pos_path.clone();

        // Add the filter to run only this specific test
        test_config.filters = vec![rel_path.to_string_lossy().to_string()];

        // Add lean flags to the rustc flags
        let lean_flags = format!(" -Flean=emit -Flean-dir={}", lean_dir.display());
        if let Some(ref existing) = test_config.target_rustcflags {
            test_config.target_rustcflags = Some(format!("{}{}", existing, lean_flags));
        } else {
            test_config.target_rustcflags = Some(lean_flags);
        }

        eprintln!("Running test {:?} with lean output to {:?}", test_path, lean_dir);

        // Catch panics so we can continue with other tests
        let result = panic::catch_unwind(|| {
            compiletest_rs::run_tests(&test_config);
        });

        if result.is_err() {
            failures.push(test_path.clone());
        }
    }

    // Report summary at the end
    eprintln!("\n\n========== SUMMARY ==========");
    eprintln!("Total tests run: {}", total_tests);
    eprintln!("Passed: {}", total_tests - failures.len());
    eprintln!("Failed: {}", failures.len());
    if !failures.is_empty() {
        eprintln!("\nFailed tests:");
        for path in &failures {
            eprintln!("  - {}", path.display());
        }
        eprintln!("=============================\n");
        panic!("{} test(s) failed", failures.len());
    } else {
        eprintln!("=============================\n");
    }
}
