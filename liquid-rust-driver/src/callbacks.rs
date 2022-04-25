use liquid_rust_common::iter::IterExt;
use liquid_rust_core::{desugar::Desugar, resolve::Resolver};
use liquid_rust_syntax::surface;
use liquid_rust_typeck::{self as typeck, global_env::GlobalEnv, wf::Wf};
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::ErrorReported;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;

use crate::{collector::SpecCollector, lowering::LoweringCtxt};

/// Compiler callbacks for Liquid Rust.
#[derive(Default)]
pub(crate) struct LiquidCallbacks;

impl Callbacks for LiquidCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        if compiler.session().has_errors() {
            return Compilation::Stop;
        }

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let _ = check_crate(tcx, compiler.session());
        });

        Compilation::Stop
    }
}

fn check_crate(tcx: TyCtxt, sess: &Session) -> Result<(), ErrorReported> {
    let specs = SpecCollector::collect(tcx, sess)?;

    let adt_defs = specs
        .adts
        .into_iter()
        .map(|(def_id, def)| {
            let mut resolver = Resolver::from_adt(tcx, def_id)?;
            Ok((def_id, resolver.resolve_adt_def(def)?))
        })
        .try_collect_exhaust()?;

    let wf = Wf::new(sess, &adt_defs);

    // Starts as raw AST
    let qualifiers: Vec<typeck::ty::Qualifier> = specs
        .qualifs
        .into_iter()
        .map(|qualifier| {
            // Resolve into core::ty
            let resolved = Resolver::resolve_qualifier(tcx, qualifier)?;
            // Check for well formedness errors
            wf.check_qualifier(&resolved)?;
            // Lower into typeck::ty
            let lowered = typeck::lowering::LoweringCtxt::lower_qualifer(&resolved);
            Ok(lowered)
        })
        .try_collect_exhaust()?;

    adt_defs
        .iter()
        .try_for_each_exhaust(|(_, def)| wf.check_adt_def(def))?;

    let fn_sigs = specs
        .fns
        .into_iter()
        .map(|(def_id, spec)| {
            let fn_sig = {
                let default_sig = surface::default_fn_sig(tcx, def_id.to_def_id());
                let fn_sig = surface::zip::zip_bare_def(spec.fn_sig, default_sig);
                Desugar::desugar(&adt_defs, fn_sig)
            };
            wf.check_fn_sig(&fn_sig)?;
            let fn_sig = typeck::lowering::LoweringCtxt::lower_fn_sig(fn_sig);
            Ok((def_id, typeck::ty::FnSpec { fn_sig, assume: spec.assume }))
        })
        .try_collect_exhaust()?;

    let genv = GlobalEnv::new(tcx, fn_sigs, adt_defs);
    let genv_specs = genv.fn_specs.borrow().clone();

    genv_specs
        .iter()
        .map(|(def_id, spec)| {
            if spec.assume {
                return Ok(());
            }
            let body = LoweringCtxt::lower(tcx, tcx.optimized_mir(*def_id))?;
            typeck::check(&genv, def_id.to_def_id(), &body, &qualifiers)
        })
        .try_collect_exhaust()
}
