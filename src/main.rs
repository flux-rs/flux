#![feature(rustc_private)]
#![feature(box_syntax)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_lint;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Config, Queries};
use rustc_lint::{LateContext, LateLintPass, LintPass};
use std::{ops::Deref, path::PathBuf, process::Command};

struct LiquidRustLintPass;

impl LiquidRustLintPass {
    fn new() -> LiquidRustLintPass {
        LiquidRustLintPass
    }
}

impl LintPass for LiquidRustLintPass {
    fn name(&self) -> &'static str {
        return stringify!(LiquidRust);
    }
}

impl<'tcx> LateLintPass<'tcx> for LiquidRustLintPass {
    fn check_crate(&mut self, cx: &LateContext<'tcx>, krate: &'tcx rustc_hir::Crate<'tcx>) {
        let _ = liquid_rust::run(cx, krate);
    }
}

struct LiquidRustDriver;

impl Callbacks for LiquidRustDriver {
    fn config(&mut self, config: &mut Config) {
        config.register_lints = Some(box move |_sess, lint_store| {
            lint_store.register_late_pass(move || box LiquidRustLintPass::new());
        });
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        _queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        Compilation::Stop
    }
}

// cli utils (copied from clippy):

/// If a command-line option matches `find_arg`, then apply the predicate `pred` on its value. If
/// true, then return it. The parameter is assumed to be either `--arg=value` or `--arg value`.
fn arg_value<'a, T: Deref<Target = str>>(
    args: &'a [T],
    find_arg: &str,
    pred: impl Fn(&str) -> bool,
) -> Option<&'a str> {
    let mut args = args.iter().map(Deref::deref);
    while let Some(arg) = args.next() {
        let mut arg = arg.splitn(2, '=');
        if arg.next() != Some(find_arg) {
            continue;
        }

        match arg.next().or_else(|| args.next()) {
            Some(v) if pred(v) => return Some(v),
            _ => {}
        }
    }
    None
}

fn toolchain_path(home: Option<String>, toolchain: Option<String>) -> Option<PathBuf> {
    home.and_then(|home| {
        toolchain.map(|toolchain| {
            let mut path = PathBuf::from(home);
            path.push("toolchains");
            path.push(toolchain);
            path
        })
    })
}

fn sys_root(orig_args: &[String]) -> Vec<String> {
    // Get the sysroot, looking from most specific to this invocation to the least:
    // - command line
    // - runtime environment
    //    - SYSROOT
    //    - RUSTUP_HOME, MULTIRUST_HOME, RUSTUP_TOOLCHAIN, MULTIRUST_TOOLCHAIN
    // - sysroot from rustc in the path
    // - compile-time environment
    //    - SYSROOT
    //    - RUSTUP_HOME, MULTIRUST_HOME, RUSTUP_TOOLCHAIN, MULTIRUST_TOOLCHAIN
    let sys_root_arg = arg_value(&orig_args, "--sysroot", |_| true);
    let have_sys_root_arg = sys_root_arg.is_some();
    let sys_root = sys_root_arg
        .map(PathBuf::from)
        .or_else(|| std::env::var("SYSROOT").ok().map(PathBuf::from))
        .or_else(|| {
            let home = std::env::var("RUSTUP_HOME")
                .or_else(|_| std::env::var("MULTIRUST_HOME"))
                .ok();
            let toolchain = std::env::var("RUSTUP_TOOLCHAIN")
                .or_else(|_| std::env::var("MULTIRUST_TOOLCHAIN"))
                .ok();
            toolchain_path(home, toolchain)
        })
        .or_else(|| {
            Command::new("rustc")
                .arg("--print")
                .arg("sysroot")
                .output()
                .ok()
                .and_then(|out| String::from_utf8(out.stdout).ok())
                .map(|s| PathBuf::from(s.trim()))
        })
        .or_else(|| option_env!("SYSROOT").map(PathBuf::from))
        .or_else(|| {
            let home = option_env!("RUSTUP_HOME")
                .or(option_env!("MULTIRUST_HOME"))
                .map(ToString::to_string);
            let toolchain = option_env!("RUSTUP_TOOLCHAIN")
                .or(option_env!("MULTIRUST_TOOLCHAIN"))
                .map(ToString::to_string);
            toolchain_path(home, toolchain)
        })
        .map(|pb| pb.to_string_lossy().to_string())
        .expect(
            "sysroot not found; please specify a SYSROOT env var, pass a --sysroot arg, or use rustup or multirust",
        );

    if !have_sys_root_arg {
        vec!["--sysroot".into(), sys_root]
    } else {
        vec![]
    }
}

fn allow_unused_doc_comments() -> Vec<String> {
    vec!["-A".into(), "unused_doc_comments".into()]
}

fn main() {
    let _ = rustc_driver::catch_fatal_errors(|| {
        // Grab the command line arguments.
        let args: Vec<_> = std::env::args_os().flat_map(|s| s.into_string()).collect();
        let args2 = args
            .iter()
            .map(|s| (*s).to_string())
            .chain(sys_root(&args).into_iter())
            .chain(allow_unused_doc_comments().into_iter())
            .collect::<Vec<_>>();

        rustc_driver::run_compiler(&args2, &mut LiquidRustDriver, None, None)
    })
    .map_err(|e| println!("{:?}", e));
}
