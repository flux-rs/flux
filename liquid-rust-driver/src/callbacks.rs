use liquid_rust_common::{errors::ErrorReported, iter::IterExt};
use liquid_rust_core::ty::context::LrCtxt;
use liquid_rust_typeck::{global_env::GlobalEnv, Checker};
use rustc_driver::{Callbacks, Compilation};
use rustc_hash::FxHashMap;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;

use crate::{collector::Collector, lowering::LoweringCtxt, wf::Wf};

/// Compiler callbacks for Liquid Rust.
#[derive(Default)]
pub(crate) struct LiquidCallbacks;

impl Callbacks for LiquidCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let _ = check_crate(tcx, &compiler.session());
        });

        Compilation::Stop
    }
}

fn check_crate(tcx: TyCtxt, sess: &Session) -> Result<(), ErrorReported> {
    let lr = LrCtxt::new();

    let annotations = Collector::collect(tcx, &sess)?;

    let fn_sigs: FxHashMap<_, _> = annotations
        .into_iter()
        .map(|(def_id, fn_sig)| Ok((def_id, Wf::check(&lr, sess, fn_sig)?)))
        .try_collect_exhaust()?;

    let global_env = GlobalEnv::new(fn_sigs);

    let mut lower_error = false;
    for (def_id, fn_sig) in &global_env.sigs {
        let body = tcx.optimized_mir(*def_id);
        match LoweringCtxt::lower(tcx, body) {
            Ok(body) => {
                Checker::check(&lr, &body, fn_sig);
            }
            Err(_) => {
                lower_error = true;
            }
        }
    }

    if lower_error {
        Err(ErrorReported)
    } else {
        Ok(())
    }
}
