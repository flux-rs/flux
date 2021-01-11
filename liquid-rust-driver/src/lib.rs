#![feature(rustc_private)]
#![feature(box_syntax)]

mod translate;
extern crate rustc_driver;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_span;
extern crate rustc_target;

use liquid_rust_typeck::{check_fn_def, Safeness};
use rustc_driver::{catch_with_exit_code, Callbacks, Compilation, RunCompiler};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::mir::MirSource;
use translate::Transformer;

pub fn run_compiler(args: Vec<String>) -> i32 {
    catch_with_exit_code(move || RunCompiler::new(&args, &mut LiquidRustDriver).run())
}

struct LiquidRustDriver;

impl Callbacks for LiquidRustDriver {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let mut compilation = Compilation::Continue;

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            for &body_id in &tcx.hir().krate().body_ids {
                let def_id = tcx.hir().body_owner_def_id(body_id);
                let body = tcx.optimized_mir(def_id);
                let mut t = Transformer::new(tcx);
                let func = t.translate_body(MirSource::item(def_id.to_def_id()), body);

                if check_fn_def(func) == Safeness::Unsafe {
                    compilation = Compilation::Stop;
                }
            }
        });
        compilation
    }
}
