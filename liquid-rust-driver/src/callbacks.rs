use crate::{collector::Collector, lower::LowerCtx};

use liquid_rust_lrir::ty;
use liquid_rust_typeck::{Checker, CheckingTask};
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::{Diagnostic, Handler};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::ParamEnv;
use rustc_mir::dataflow::{
    impls::MaybeUninitializedPlaces, move_paths::MoveData, Analysis, MoveDataParamEnv,
};

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
                match LowerCtx::lower_body(tcx, body) {
                    Ok(lrir_body) => {
                        let param_env = tcx.param_env(body.source.def_id());
                        let move_data = MoveData::gather_moves(body, tcx, param_env).unwrap();
                        let mdpe = mk_mpde(
                            MoveData::gather_moves(body, tcx, param_env).unwrap(),
                            param_env,
                        );

                        let flow_uninit = MaybeUninitializedPlaces::new(tcx, body, &mdpe)
                            .into_engine(tcx, body)
                            .iterate_to_fixpoint();

                        let task = CheckingTask::new(&lrir_body, fn_decl, move_data, flow_uninit);

                        Checker::check(task, &lr_tcx);
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

fn mk_mpde<'tcx>(move_data: MoveData<'tcx>, param_env: ParamEnv<'tcx>) -> MoveDataParamEnv<'tcx> {
    // FIXME: Ugly hack, but we need a MoveDataParamEnv to call the mir dataflow and
    // fields in MoveDataParamEnv are private.
    struct MPDE<'tcx> {
        move_data: MoveData<'tcx>,
        param_env: ParamEnv<'tcx>,
    }
    let res = MPDE {
        move_data,
        param_env,
    };

    unsafe { std::mem::transmute::<MPDE<'tcx>, MoveDataParamEnv<'tcx>>(res) }
}
