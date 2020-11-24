#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;

mod lower;
mod visitor;

use lower::LowerCtx;
use visitor::DefIdCollector;

use liquid_rust_common::ir::Program;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};

struct CompilerCalls;

impl Callbacks for CompilerCalls {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let mut visitor = DefIdCollector::new(tcx);
            tcx.hir().krate().visit_all_item_likes(&mut visitor);
            let annotations = visitor.annotations();

            let mut builder = Program::builder(annotations.len());

            for (func_id, (def_id, ty)) in builder.func_ids().zip(annotations) {
                let mut lcx = LowerCtx::new(tcx);
                let body = tcx.optimized_mir(def_id);

                let mut func_builder = lcx.lower_body(body).unwrap();

                if let Some(ty) = ty {
                    func_builder.add_ty(ty);
                }

                let func = func_builder.build().unwrap();

                builder.add_func(func_id, func);
            }

            let program = builder.build().unwrap();

            println!("{}", program);

            liquid_rust_tycheck::check_program(&program);
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
        rustc_driver::RunCompiler::new(&args, callbacks).run()
    });

    std::process::exit(exit_code)
}

fn main() {
    env_logger::init();
    run_compiler(std::env::args().collect::<Vec<_>>(), &mut CompilerCalls);
}
