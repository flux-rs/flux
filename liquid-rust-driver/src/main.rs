#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_span;

mod lower;
mod visitor;

use lower::LowerCtx;
use visitor::DefIdCollector;

use liquid_rust_mir::Program;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::bug;

struct CompilerCalls;

impl Callbacks for CompilerCalls {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let mut compilation = Compilation::Continue;

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let mut visitor = DefIdCollector::new(tcx);
            tcx.hir().krate().visit_all_item_likes(&mut visitor);
            let annotations = visitor.annotations();

            let mut builder = Program::builder(annotations.len());

            for (func_id, (def_id, ty)) in builder.func_ids().zip(annotations) {
                let mut lcx = LowerCtx::new(tcx);
                let body = tcx.optimized_mir(def_id);

                let mut func_builder = match lcx.lower_body(body) {
                    Ok(builder) => builder,
                    Err(err) => {
                        compiler
                            .session()
                            .diagnostic()
                            .struct_span_fatal(err.span(), &err.to_string())
                            .note("several rust constructs are not supported by liquid rust (yet).")
                            .emit();

                        compilation = Compilation::Stop;
                        continue;
                    }
                };

                if let Some(ty) = ty {
                    match ty {
                        Ok(ty) => func_builder.add_ty(ty),
                        Err(err) => {
                            let mut builder = compiler.session().diagnostic().struct_span_fatal(
                                *err.span(),
                                &format!("error while parsing type annotation: {}", err),
                            );

                            if let Some(help) = err.help() {
                                builder.help(help);
                            }

                            builder.emit();
                            compilation = Compilation::Stop;
                            continue;
                        }
                    }
                }

                let func = match func_builder.build() {
                    Ok(func) => func,
                    Err(bb_id) => bug!("Basic Block `{}` is missing.", bb_id),
                };

                builder.add_func(func_id, func);
            }

            if let Compilation::Continue = compilation {
                let program = match builder.build() {
                    Ok(program) => program,
                    Err(func_id) => bug!("Function `{}` is missing.", func_id),
                };

                println!("{}", program);
                liquid_rust_tycheck::check_program(&program);
            }
        });

        compilation
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
