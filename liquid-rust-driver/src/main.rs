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

use lower::{LowerCtx, LowerMap};
use visitor::DefIdCollector;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};

use std::collections::HashMap;

use liquid_rust_lang::{ir::FuncId, tycheck::TyContext};

struct CompilerCalls;

impl Callbacks for CompilerCalls {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let mut funcs = HashMap::new();
        let mut func_ids = LowerMap::<_, FuncId>::new();
        let mut annotations = HashMap::new();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let mut visitor = DefIdCollector::new(tcx, &mut annotations, &mut func_ids);
            tcx.hir().krate().visit_all_item_likes(&mut visitor);

            for (&def_id, &func_id) in func_ids.iter() {
                let mut lcx = LowerCtx::new(tcx, &func_ids);
                let body = tcx.optimized_mir(def_id);
                let func = lcx.lower_body(body).unwrap();
                println!("{} = {}", func_id, func);
                funcs.insert(func_id, func);
            }
        });

        let _tcx = TyContext::new(funcs, annotations).unwrap();

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
    run_compiler(std::env::args().collect::<Vec<_>>(), &mut CompilerCalls);
}
