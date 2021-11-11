use liquid_rust_common::{errors::ErrorReported, iter::IterExt};
use liquid_rust_core::wf::Wf;
use liquid_rust_typeck::{global_env::GlobalEnv, Checker};
use rustc_driver::{Callbacks, Compilation};
use rustc_hash::FxHashMap;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;

use crate::{collector::Collector, lowering::LoweringCtxt, resolve::Resolver};

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
    let annotations = Collector::collect(tcx, sess)?;

    let resolver = Resolver::new(sess);
    let wf = Wf::new(sess);
    let fn_sigs: FxHashMap<_, _> = annotations
        .into_iter()
        .map(|(def_id, fn_sig)| {
            let fn_sig = resolver.resolve(fn_sig)?;
            wf.check_fn_sig(&fn_sig)?;
            Ok((def_id, fn_sig))
        })
        .try_collect_exhaust()?;

    let global_env = GlobalEnv::new(fn_sigs);
    global_env
        .sigs
        .iter()
        .map(|(def_id, fn_sig)| {
            println!("#######################################");
            println!("CHECKING: {}", tcx.item_name(*def_id));
            println!("#######################################");
            let body = LoweringCtxt::lower(tcx, tcx.optimized_mir(*def_id))?;
            Checker::check(&global_env, sess, &body, fn_sig)
        })
        .try_collect_exhaust()
}
