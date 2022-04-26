use liquid_rust_common::iter::IterExt;
use liquid_rust_core::{self as core, desugar};
use liquid_rust_syntax::{self as syntax, surface};
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

    let mut genv = GlobalEnv::new(tcx);

    // Register structs parameters
    specs.adts.iter().try_for_each_exhaust(|(def_id, def)| {
        if let Some(refined_by) = &def.refined_by {
            genv.register_refined_by(
                def_id.to_def_id(),
                desugar::desugar_params(sess, refined_by)?,
            );
        }
        Ok(())
    })?;

    // Qualifiers
    let qualifiers: Vec<typeck::ty::Qualifier> = specs
        .qualifs
        .into_iter()
        .map(|qualifier| {
            let qualifier = desugar::desugar_qualifier(sess, qualifier)?;
            Wf::new(sess, &genv).check_qualifier(&qualifier)?;
            Ok(typeck::lowering::LoweringCtxt::lower_qualifer(&qualifier))
        })
        .try_collect_exhaust()?;

    // Adt definitions
    specs
        .adts
        .into_iter()
        .try_for_each_exhaust(|(def_id, adt_def)| {
            let mut resolver = syntax::resolve::Resolver::from_adt(tcx, def_id)?;
            let adt_def = resolver.resolve_adt_def(adt_def)?;
            let adt_def = desugar::desugar_adt(sess, adt_def)?;
            Wf::new(sess, &genv).check_adt_def(&adt_def)?;
            genv.register_adt_def(def_id.to_def_id(), adt_def);
            Ok(())
        })?;

    // Function signatures
    specs
        .fns
        .into_iter()
        .try_for_each_exhaust(|(def_id, spec)| {
            let fn_sig = {
                let default_sig = surface::default_fn_sig(tcx, def_id.to_def_id());
                let fn_sig = surface::zip::zip_bare_def(spec.fn_sig, default_sig);
                desugar::desugar_fn_sig(sess, &genv, fn_sig)?
            };
            Wf::new(sess, &genv).check_fn_sig(&fn_sig)?;
            let spec = core::ty::FnSpec { fn_sig, assume: spec.assume };
            genv.register_fn_spec(def_id.to_def_id(), spec);
            Ok(())
        })?;

    let genv_specs = genv.fn_specs.borrow().clone();

    genv_specs
        .iter()
        .map(|(def_id, spec)| {
            if spec.assume {
                return Ok(());
            }
            let body = LoweringCtxt::lower(tcx, tcx.optimized_mir(*def_id))?;
            typeck::check(&genv, *def_id, &body, &qualifiers)
        })
        .try_collect_exhaust()
}
