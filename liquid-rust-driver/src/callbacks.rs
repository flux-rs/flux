use liquid_rust_common::iter::IterExt;
use liquid_rust_core::{self as core, desugar, resolve::Resolver};
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
    for (def_id, def) in &specs.adts {
        if let Some(refined_by) = &def.refined_by {
            genv.register_refined_by(def_id.to_def_id(), desugar::desugar_params(refined_by));
        }
    }

    // Qualifiers
    let qualifiers: Vec<typeck::ty::Qualifier> = specs
        .qualifs
        .into_iter()
        .map(|qualifier| {
            let resolved = Resolver::resolve_qualifier(tcx, qualifier)?;
            Wf::new(sess, &genv).check_qualifier(&resolved)?;
            Ok(typeck::lowering::LoweringCtxt::lower_qualifer(&resolved))
        })
        .try_collect_exhaust()?;

    // Adt definitions
    for (def_id, adt_def) in specs.adts {
        let mut resolver = syntax::resolve::Resolver::from_adt(tcx, def_id)?;
        let adt_def = resolver.resolve_adt_def(adt_def)?;
        let adt_def = desugar::desugar_adt(&genv, adt_def);
        Wf::new(sess, &genv).check_adt_def(&adt_def)?;
        genv.register_adt_def(def_id.to_def_id(), adt_def);
    }

    // Function signatures
    for (def_id, spec) in specs.fns {
        let fn_sig = {
            let default_sig = surface::default_fn_sig(tcx, def_id.to_def_id());
            let fn_sig = surface::zip::zip_bare_def(spec.fn_sig, default_sig);
            desugar::desugar_fn_sig(&genv, fn_sig)
        };
        Wf::new(sess, &genv).check_fn_sig(&fn_sig)?;
        let spec = core::ty::FnSpec { fn_sig, assume: spec.assume };
        genv.register_fn_spec(def_id.to_def_id(), spec);
    }

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
