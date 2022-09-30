use flux_common::iter::IterExt;
use flux_desugar as desugar;
use flux_errors::FluxSession;
use flux_middle::{
    core::{AdtSortInfo, AdtSorts},
    global_env::{ConstInfo, GlobalEnv},
    rustc, ty,
};
use flux_syntax::surface;
use flux_typeck::{self as typeck, wf::Wf};
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashSet;
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::{
    query::{query_values, Providers},
    TyCtxt, WithOptConstParam,
};
use rustc_session::config::ErrorOutputType;

use crate::{
    collector::{IgnoreKey, Ignores, SpecCollector},
    mir_storage,
};

#[derive(Default)]
pub(crate) struct FluxCallbacks {
    error_format: ErrorOutputType,
}

impl Callbacks for FluxCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        assert!(config.override_queries.is_none());
        self.error_format = config.opts.error_format;
        config.override_queries = Some(|_, local, _| {
            local.mir_borrowck = mir_borrowck;
        });
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        if compiler.session().has_errors().is_some() {
            return Compilation::Stop;
        }

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let sess = FluxSession::new(self.error_format, tcx.sess.parse_sess.clone_source_map());
            let _ = check_crate(tcx, &sess);
            sess.finish_diagnostics();
        });

        Compilation::Stop
    }
}

fn check_crate(tcx: TyCtxt, sess: &FluxSession) -> Result<(), ErrorGuaranteed> {
    let mut genv = GlobalEnv::new(tcx, sess);

    let ck = CrateChecker::new(&mut genv)?;

    if ck.ignores.contains(&IgnoreKey::Crate) {
        return Ok(());
    }

    let crate_items = tcx.hir_crate_items(());
    let items = crate_items.items().map(|item| item.def_id);
    let impl_items = crate_items.impl_items().map(|impl_item| impl_item.def_id);

    items
        .chain(impl_items)
        .filter(|def_id| !ck.is_assumed(*def_id) && !is_ignored(tcx, &ck.ignores, *def_id))
        .try_for_each_exhaust(|def_id| ck.check_item(def_id))
}

struct CrateChecker<'a, 'genv, 'tcx> {
    genv: &'a mut GlobalEnv<'genv, 'tcx>,
    qualifiers: Vec<ty::Qualifier>,
    assume: FxHashSet<LocalDefId>,
    ignores: Ignores,
}

/// `is_ignored` transitively follows the `def_id` 's parent-chain to check if
/// any enclosing mod has been marked as `ignore`
fn is_ignored(tcx: TyCtxt, ignores: &Ignores, def_id: LocalDefId) -> bool {
    let parent_def_id = tcx.parent_module_from_def_id(def_id);
    if parent_def_id == def_id {
        false
    } else {
        ignores.contains(&IgnoreKey::Module(parent_def_id))
            || is_ignored(tcx, ignores, parent_def_id)
    }
}

impl<'a, 'genv, 'tcx> CrateChecker<'a, 'genv, 'tcx> {
    fn new(genv: &'a mut GlobalEnv<'genv, 'tcx>) -> Result<Self, ErrorGuaranteed> {
        let specs = SpecCollector::collect(genv.tcx, genv.sess)?;

        let mut assume = FxHashSet::default();
        let mut adt_sorts = AdtSorts::default();

        // Ignore everything and go home
        if specs.ignores.contains(&IgnoreKey::Crate) {
            return Ok(CrateChecker { genv, qualifiers: vec![], assume, ignores: specs.ignores });
        }

        // gather consts
        specs
            .consts
            .into_iter()
            .try_for_each_exhaust(|(def_id, const_sig)| {
                if !is_ignored(genv.tcx, &specs.ignores, def_id) {
                    let did = def_id.to_def_id();
                    let sym = def_id_symbol(genv.tcx, def_id);
                    genv.consts
                        .push(ConstInfo { def_id: did, sym, val: const_sig.val });
                }
                Ok(())
            })?;

        // TODO:UF gather UFs
        specs
            .uifs
            .into_iter()
            .try_for_each_exhaust(|(sym, uf_def)| {
                let uf_def = desugar::resolve_uf_def(genv.sess, uf_def)?;
                genv.register_uf_def(sym, uf_def);
                Ok(())
            })?;

        // Register adts
        specs.structs.iter().try_for_each_exhaust(|(def_id, def)| {
            if let Some(refined_by) = &def.refined_by {
                register_adt_info(genv.sess, &mut adt_sorts, def_id, refined_by)?;
                genv.register_adt_def(
                    def_id.to_def_id(),
                    adt_sorts.get_sorts(def_id.to_def_id()).unwrap(),
                );
            }
            Ok(())
        })?;
        specs.enums.iter().try_for_each_exhaust(|(def_id, def)| {
            if let Some(refined_by) = &def.refined_by {
                register_adt_info(genv.sess, &mut adt_sorts, def_id, refined_by)?;
                genv.register_adt_def(
                    def_id.to_def_id(),
                    adt_sorts.get_sorts(def_id.to_def_id()).unwrap(),
                );
            }
            Ok(())
        })?;
        genv.finish_adt_registration();

        // Qualifiers
        let qualifiers: Vec<ty::Qualifier> = specs
            .qualifs
            .into_iter()
            .map(|qualifier| {
                let qualifier =
                    desugar::desugar_qualifier(genv.sess, &genv.consts, qualifier, &adt_sorts)?;
                Wf::new(genv).check_qualifier(&qualifier)?;
                Ok(ty::conv::ConvCtxt::conv_qualifier(&qualifier))
            })
            .try_collect_exhaust()?;

        // Assert behavior from Crate config
        // TODO(atgeller) rest of settings from crate config
        if let Some(crate_config) = specs.crate_config {
            let assert_behavior = crate_config.check_asserts;
            genv.register_assert_behavior(assert_behavior);
        }

        // Adt definitions
        specs
            .structs
            .into_iter()
            .try_for_each_exhaust(|(def_id, struct_def)| {
                let adt_def = desugar::desugar_struct_def(genv, struct_def)?;
                Wf::new(genv).check_struct_def(&adt_def)?;
                genv.register_struct_def(def_id.to_def_id(), adt_def);
                Ok(())
            })?;

        specs
            .enums
            .into_iter()
            .try_for_each_exhaust(|(def_id, enum_def)| {
                let enum_def = desugar::desugar_enum_def(genv, &adt_sorts, enum_def)?;
                genv.register_enum_def(def_id.to_def_id(), enum_def);
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
                if !is_ignored(genv.tcx, &specs.ignores, def_id) {
                    if let Some(fn_sig) = spec.fn_sig {
                        let fn_sig = surface::expand::expand_sig(&aliases, fn_sig);
                        let fn_sig = desugar::desugar_fn_sig(genv, &adt_sorts, def_id, fn_sig)?;
                        Wf::new(genv).check_fn_sig(&fn_sig)?;
                        genv.register_fn_sig(def_id.to_def_id(), fn_sig);
                    }
                }
                Ok(())
            })?;

        Ok(CrateChecker { genv, qualifiers, assume, ignores: specs.ignores })
    }

    fn is_assumed(&self, def_id: LocalDefId) -> bool {
        self.assume.contains(&def_id)
    }

    fn check_fn(&self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        let mir = unsafe { mir_storage::retrieve_mir_body(self.genv.tcx, def_id).body };

        if flux_common::config::CONFIG.dump_mir {
            let mut w = std::io::BufWriter::new(std::io::stdout());
            rustc_middle::mir::pretty::write_mir_fn(
                self.genv.tcx,
                &mir,
                &mut |_, _| Ok(()),
                &mut w,
            )
            .unwrap();
        }

        let body = rustc::lowering::LoweringCtxt::lower_mir_body(self.genv.tcx, mir)?;

        typeck::check(self.genv, def_id.to_def_id(), &body, &self.qualifiers)
    }

    fn check_item(&self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        match self.genv.tcx.def_kind(def_id.to_def_id()) {
            DefKind::Fn | DefKind::AssocFn => self.check_fn(def_id),
            _ => Ok(()),
        }
    }
}

fn register_adt_info(
    sess: &FluxSession,
    adt_sorts: &mut AdtSorts,
    def_id: &LocalDefId,
    refined_by: &surface::Params,
) -> Result<(), ErrorGuaranteed> {
    let sorts = desugar::resolve_sorts(sess, refined_by)?;
    let fields = refined_by.iter().map(|p| p.name.name).collect();
    let info = AdtSortInfo { fields, sorts };
    adt_sorts.insert(def_id.to_def_id(), info);
    Ok(())
}

fn def_id_symbol(tcx: TyCtxt, def_id: LocalDefId) -> rustc_span::Symbol {
    let did = def_id.to_def_id();
    let def_path = tcx.def_path(did);
    if let Some(dp) = def_path.data.last() {
        if let rustc_hir::definitions::DefPathData::ValueNs(sym) = dp.data {
            return sym;
        }
    }
    panic!("def_id_symbol fails on {did:?}")
}

#[allow(clippy::needless_lifetimes)]
fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> query_values::mir_borrowck<'tcx> {
    let body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
        tcx,
        WithOptConstParam::unknown(def_id),
    );
    // SAFETY: This is safe because we are feeding in the same `tcx` that is
    // going to be used as a witness when pulling out the data.
    unsafe {
        mir_storage::store_mir_body(tcx, def_id, body_with_facts);
    }
    let mut providers = Providers::default();
    rustc_borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}
