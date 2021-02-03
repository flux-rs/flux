#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(or_patterns)]

mod lower;
mod translate;
mod visitor;

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
#[macro_use]
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_span;
extern crate rustc_target;

use visitor::DefCollector;

use liquid_rust_typeck::check_fn_def;
use rustc_driver::{catch_with_exit_code, Callbacks, Compilation, RunCompiler};
use rustc_interface::{interface::Compiler, Queries};
use translate::Transformer;

pub fn run_compiler(args: Vec<String>) -> i32 {
    catch_with_exit_code(move || RunCompiler::new(&args, &mut LiquidRustDriver).run())
}

struct LiquidRustDriver;

impl Callbacks for LiquidRustDriver {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let handler = compiler.session().diagnostic();
        let mut buffer = Vec::new();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let mut visitor = DefCollector::new(tcx, handler, &mut buffer);
            tcx.hir().krate().visit_all_item_likes(&mut visitor);
            let mut annotations = visitor.annotations();

            if !buffer.is_empty() {
                // compilation = Compilation::Stop;

                for diagnostic in buffer.drain(..) {
                    handler.emit_diagnostic(&diagnostic);
                }
            }

            for &body_id in &tcx.hir().krate().body_ids {
                let def_id = tcx.hir().body_owner_def_id(body_id);
                let body = tcx.optimized_mir(def_id);
                let func = Transformer::translate(tcx, &mut annotations, body);
                // println!("{}", func);

                match check_fn_def(func) {
                    Ok(safeness) => {
                        println!("{}", safeness);
                    }
                    Err(errs) => {
                        println!("{:?}", errs);
                    }
                }
            }
        });
        Compilation::Stop
    }
}
