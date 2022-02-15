use liquid_rust_common::{errors::ErrorReported, iter::IterExt};
use liquid_rust_typeck::{
    self as typeck,
    global_env::{FnSpec, GlobalEnv},
    wf::Wf,
};
use rustc_driver::{Callbacks, Compilation};
use rustc_hash::FxHashMap;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use typeck::global_env::AdtDefs;

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
    let specs = SpecCollector::collect(tcx, sess)?;

    let adt_defs: AdtDefs = specs
        .adts
        .into_iter()
        .map(|(def_id, spec)| Ok((def_id, Resolver::resolve_adt_def(tcx, spec.refined_by)?)))
        .try_collect_exhaust()?;

    let wf = Wf::new(sess, &adt_defs);
    let fn_sigs: FxHashMap<_, _> = specs
        .fns
        .into_iter()
        .map(|(def_id, spec)| {
            let fn_sig = Resolver::resolve(tcx, def_id, spec.fn_sig)?;
            wf.check_fn_sig(&fn_sig)?;
            Ok((def_id, FnSpec { fn_sig, assume: spec.assume }))
        })
        .try_collect_exhaust()?;

    let global_env = GlobalEnv::new(tcx, fn_sigs, adt_defs);
    global_env
        .fn_specs
        .iter()
        .map(|(def_id, spec)| {
            if spec.assume {
                return Ok(());
            }
            let body = LoweringCtxt::lower(tcx, tcx.optimized_mir(*def_id))?;
            typeck::check(&global_env, def_id.to_def_id(), &body)
        })
        .try_collect_exhaust()
}
