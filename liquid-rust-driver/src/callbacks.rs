use liquid_rust_common::iter::IterExt;
use liquid_rust_core::desugar;
use liquid_rust_syntax::{self as syntax, surface};
use liquid_rust_typeck::{self as typeck, global_env::GlobalEnv, wf::Wf};
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::ErrorReported;
use rustc_hash::FxHashSet;
use rustc_hir::{def_id::LocalDefId, itemlikevisit::ItemLikeVisitor, ImplItemKind, ItemKind};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;

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
            let _ = check_crate(tcx);
        });

        Compilation::Stop
    }
}

fn check_crate(tcx: TyCtxt) -> Result<(), ErrorReported> {
    let mut ck = CrateChecker::new(tcx)?;

    tcx.hir().visit_all_item_likes(&mut ck);

    if ck.error_reported {
        Err(ErrorReported)
    } else {
        Ok(())
    }
}

struct CrateChecker<'tcx> {
    genv: GlobalEnv<'tcx>,
    qualifiers: Vec<typeck::ty::Qualifier>,
    assume: FxHashSet<LocalDefId>,
    error_reported: bool,
}

impl<'tcx> CrateChecker<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Result<CrateChecker, ErrorReported> {
        let sess = tcx.sess;
        let specs = SpecCollector::collect(tcx, sess)?;

        let mut assume = FxHashSet::default();
        let mut genv = GlobalEnv::new(tcx);

        // Register adt sorts
        specs.structs.iter().try_for_each_exhaust(|(def_id, def)| {
            if let Some(refined_by) = &def.refined_by {
                genv.register_adt_sorts(
                    def_id.to_def_id(),
                    desugar::resolve_sorts(sess, refined_by)?,
                );
            }
            Ok(())
        })?;
        specs.enums.iter().try_for_each_exhaust(|(def_id, def)| {
            if let Some(refined_by) = &def.refined_by {
                genv.register_adt_sorts(
                    def_id.to_def_id(),
                    desugar::resolve_sorts(sess, refined_by)?,
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
            .structs
            .into_iter()
            .try_for_each_exhaust(|(def_id, struct_def)| {
                let mut resolver = syntax::resolve::Resolver::from_adt(tcx, def_id)?;
                let struct_def = resolver.resolve_struct_def(struct_def)?;
                let adt_def = desugar::desugar_struct_def(sess, struct_def)?;
                Wf::new(sess, &genv).check_adt_def(&adt_def)?;
                genv.register_adt_def(def_id.to_def_id(), adt_def);
                Ok(())
            })?;
        specs
            .enums
            .into_iter()
            .try_for_each_exhaust(|(def_id, enum_def)| {
                let adt_def = desugar::desugar_enum_def(tcx, enum_def)?;
                Wf::new(sess, &genv).check_adt_def(&adt_def)?;
                genv.register_adt_def(def_id.to_def_id(), adt_def);
                Ok(())
            })?;

        let aliases = specs.aliases;

        // Function signatures
        specs
            .fns
            .into_iter()
            .try_for_each_exhaust(|(def_id, spec)| {
                if spec.assume {
                    assume.insert(def_id);
                }
                if let Some(fn_sig) = spec.fn_sig {
                    let fn_sig = surface::expand::expand_sig(&aliases, fn_sig);
                    let default_sig = surface::default_fn_sig(tcx, def_id.to_def_id());
                    let fn_sig = surface::zip::zip_bare_def(fn_sig, default_sig);
                    let fn_sig = desugar::desugar_fn_sig(sess, &genv, fn_sig)?;
                    Wf::new(sess, &genv).check_fn_sig(&fn_sig)?;
                    genv.register_fn_sig(def_id.to_def_id(), fn_sig);
                }
                Ok(())
            })?;

        Ok(CrateChecker { genv, qualifiers, assume, error_reported: false })
    }

    fn check_fn(&self, def_id: LocalDefId) -> Result<(), ErrorReported> {
        if self.assume.contains(&def_id) {
            return Ok(());
        }
        let mir = &self.genv.tcx.optimized_mir(def_id);
        let body = LoweringCtxt::lower(self.genv.tcx, mir)?;
        typeck::check(&self.genv, def_id.to_def_id(), &body, &self.qualifiers)
    }
}

impl<'tcx> ItemLikeVisitor<'tcx> for CrateChecker<'tcx> {
    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        if let ItemKind::Fn(..) = &item.kind {
            if self.check_fn(item.def_id).is_err() {
                self.error_reported = true;
            }
        }
    }

    fn visit_impl_item(&mut self, item: &'tcx rustc_hir::ImplItem<'tcx>) {
        if let ImplItemKind::Fn(..) = &item.kind {
            if self.check_fn(item.def_id).is_err() {
                self.error_reported = true;
            }
        }
    }

    fn visit_trait_item(&mut self, _item: &'tcx rustc_hir::TraitItem<'tcx>) {}
    fn visit_foreign_item(&mut self, _item: &'tcx rustc_hir::ForeignItem<'tcx>) {}
}
