use crate::{bbenv_builder::BBEnvBuilder, collector::Collector, lower::LowerCtx};

use liquid_rust_lrir::ty;
use liquid_rust_typeck::Checker;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::{Diagnostic, Handler};
use rustc_interface::{interface::Compiler, Queries};

/// Compiler callbacks for Liquid Rust.
#[derive(Default)]
pub(crate) struct LiquidCallbacks;

impl LiquidCallbacks {
    fn emit_diagnostics(mut diagnostics: Vec<Diagnostic>, handler: &Handler) {
        for diagnostic in diagnostics.drain(..) {
            handler.emit_diagnostic(&diagnostic);
        }
    }
}

impl Callbacks for LiquidCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let handler = compiler.session().diagnostic();
        let mut diagnostics = Vec::new();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let lr_tcx = ty::TyCtxt::new();
            let annotations = Collector::collect(&lr_tcx, tcx, handler, &mut diagnostics);

            for (def_id, fn_decl) in &annotations {
                let body = tcx.optimized_mir(*def_id);
                let bb_envs = BBEnvBuilder::build_envs_for_body(body, fn_decl, &lr_tcx, tcx);
                match LowerCtx::lower_body(tcx, body) {
                    Ok(lrir_body) => {
                        Checker::check(&lrir_body, fn_decl, &bb_envs, &lr_tcx);
                    }
                    Err(_) => {
                        todo!()
                    }
                };
            }

            Self::emit_diagnostics(diagnostics, handler);
        });

        Compilation::Stop
    }
}
