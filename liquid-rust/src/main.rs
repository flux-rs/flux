#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_mir;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::ItemKind;
use rustc_interface::{interface::Compiler, Queries};
use rustc_mir::util::write_mir_pretty;

struct CompilerCalls;

impl Callbacks for CompilerCalls {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let hir = tcx.hir();

            for (&hir_id, item) in &tcx.hir().krate().items {
                if let ItemKind::Fn(_, _, _) = item.kind {
                    let def_id = hir.local_def_id(hir_id);
                    // let _mir = tcx.optimized_mir(def_id);
                    println!("{:?}", hir.attrs(hir_id));
                    write_mir_pretty(tcx, Some(def_id.to_def_id()), &mut std::io::stdout())
                        .unwrap();
                }
            }
        });

        Compilation::Continue
    }
}

fn compile_time_sysroot() -> Option<String> {
    if option_env!("RUSTC_STAGE").is_some() {
        return None;
    }
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    Some(match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("To build Miri without rustup, set the `RUST_SYSROOT` env var at build time")
            .to_owned(),
    })
}

fn run_compiler(mut args: Vec<String>, callbacks: &mut (dyn Callbacks + Send)) -> ! {
    if let Some(sysroot) = compile_time_sysroot() {
        let sysroot_flag = "--sysroot";
        if !args.iter().any(|e| e == sysroot_flag) {
            args.push(sysroot_flag.to_owned());
            args.push(sysroot);
        }
    }

    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::run_compiler(&args, callbacks, None, None, None)
    });

    std::process::exit(exit_code)
}

fn main() {
    run_compiler(std::env::args().collect::<Vec<_>>(), &mut CompilerCalls);
}
