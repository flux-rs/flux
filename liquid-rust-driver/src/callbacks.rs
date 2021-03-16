use crate::collector::Collector;

use liquid_rust_lrir::ty;
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

            Self::emit_diagnostics(diagnostics, handler);
        });

        Compilation::Stop
    }
}
