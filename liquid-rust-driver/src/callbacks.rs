use liquid_rust_common::{errors::ErrorReported, iter::IterExt};
use liquid_rust_core::wf::Wf;
use liquid_rust_typeck::{
    self as typeck,
    global_env::{FnSpec, GlobalEnv},
};
use rustc_driver::{Callbacks, Compilation};
use rustc_hash::FxHashMap;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;

use crate::{collector::SpecCollector, lowering::LoweringCtxt, resolve::Resolver};

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
            let _ = check_crate(tcx, compiler.session());
        });

        Compilation::Stop
    }
}

fn check_crate(tcx: TyCtxt, sess: &Session) -> Result<(), ErrorReported> {
    let annotations = SpecCollector::collect(tcx, sess)?;

    let wf = Wf::new(sess);
    let fn_sigs: FxHashMap<_, _> = annotations
        .into_iter()
        .map(|(def_id, spec)| {
            let fn_sig = Resolver::resolve(tcx, def_id, spec.fn_sig)?;
            wf.check_fn_sig(&fn_sig)?;
            Ok((
                def_id,
                FnSpec {
                    fn_sig,
                    assume: spec.assume,
                },
            ))
        })
        .try_collect_exhaust()?;

    let global_env = GlobalEnv::new(tcx, fn_sigs);
    global_env
        .specs
        .iter()
        .map(|(def_id, spec)| {
            if spec.assume {
                return Ok(Default::default());
            }
            let body = LoweringCtxt::lower(tcx, tcx.optimized_mir(*def_id))?;
            typeck::check(&global_env, def_id.to_def_id(), &body)
        })
        .try_collect_exhaust()
}
