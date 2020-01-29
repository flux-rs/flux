#![feature(rustc_private)]
#![feature(box_syntax)]
// #![allow(unused_imports)]
#![allow(dead_code)]
// #![allow(unused_variables)]

mod context;
mod refinements;

extern crate rustc;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_session;
extern crate rustc_span;
extern crate syntax;

use context::LiquidRustContext;
use rustc_interface::Config;
use rustc_lint::{LateContext, LateLintPass, LintPass};

struct LiquidRust;

impl LiquidRust {
    fn new() -> LiquidRust {
        LiquidRust
    }
}

impl LintPass for LiquidRust {
    fn name(&self) -> &'static str {
        return stringify!(LiquidRust);
    }
}

impl<'a, 'tcx> LateLintPass<'a, 'tcx> for LiquidRust {
    fn check_crate(
        &mut self,
        late_cx: &LateContext<'a, 'tcx>,
        krate: &'tcx rustc_hir::Crate<'tcx>,
    ) {
        let cx = &LiquidRustContext::new(late_cx);
        let _ = refinements::collect_type_annots(cx, krate);
    }
}

struct LiquidRustDriver;

impl rustc_driver::Callbacks for LiquidRustDriver {
    fn config(&mut self, config: &mut Config) {
        config.register_lints = Some(box move |_sess, lint_store| {
            lint_store.register_late_pass(move || box LiquidRust::new());
        });
    }
}

fn sys_root() -> Vec<String> {
    let home = option_env!("RUSTUP_HOME");
    let toolchain = option_env!("RUSTUP_TOOLCHAIN");
    let sysroot = format!("{}/toolchains/{}", home.unwrap(), toolchain.unwrap());
    vec!["--sysroot".into(), sysroot]
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
            .chain(sys_root().into_iter())
            .chain(allow_unused_doc_comments().into_iter())
            .collect::<Vec<_>>();

        rustc_driver::run_compiler(&args2, &mut LiquidRustDriver, None, None)
    })
    .map_err(|e| println!("{:?}", e));
}
