use crate::{lower::LowerCtx, visitor::DefCollector};

use liquid_rust_mir::{ty::Ty, FuncId, Program};

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::DefId;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::bug;

use std::collections::HashMap;

/// Compiler callbacks for liquid rust.
pub(crate) struct CompilerCalls;

impl Callbacks for CompilerCalls {
    /// Liquid rust always runs after analysis so we can be sure the underlying rust program is
    /// valid according to the compiler.
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let mut compilation = Compilation::Continue;

        let handler = compiler.session().diagnostic();
        let mut buffer = Vec::new();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let mut visitor = DefCollector::new(tcx, handler, &mut buffer);
            tcx.hir().krate().visit_all_item_likes(&mut visitor);
            let annotations = visitor.annotations();

            if !buffer.is_empty() {
                compilation = Compilation::Stop;

                for diagnostic in buffer.drain(..) {
                    handler.emit_diagnostic(&diagnostic);
                }
            }

            let mut builder = Program::builder(annotations.len());

            let func_ids: HashMap<DefId, FuncId> = annotations
                .iter()
                .map(|(def_id, _)| *def_id)
                .zip(builder.func_ids())
                .collect();

            for (func_id, (def_id, ty)) in builder.func_ids().zip(annotations) {
                let body = tcx.optimized_mir(def_id);
                let lcx = LowerCtx::new(tcx, body, &func_ids);

                let mut func_builder = match lcx.lower_body() {
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

                match ty {
                    Ty::Func(ty) => func_builder.add_ty(ty),
                    Ty::Refined(_, _) => {
                        handler.struct_fatal("expected function type").emit();
                        compilation = Compilation::Stop;
                        continue;
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
