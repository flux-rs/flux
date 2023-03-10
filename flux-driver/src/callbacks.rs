use desugar::annot_check;
use flux_common::{cache::QueryCache, dbg, iter::IterExt};
use flux_config as config;
use flux_desugar as desugar;
use flux_errors::FluxSession;
use flux_metadata::CStore;
use flux_middle::{
    early_ctxt::EarlyCtxt,
    fhir::{self, ConstInfo},
    global_env::GlobalEnv,
    rustc,
};
use flux_refineck::{self as refineck, wf::Wf};
use flux_syntax::surface;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::{
    query::{query_values, Providers},
    TyCtxt, WithOptConstParam,
};
use rustc_session::config::OutputType;

use crate::collector::{IgnoreKey, Ignores, SpecCollector, Specs};

pub(crate) struct FluxCallbacks {
    full_compilation: bool,
}

impl FluxCallbacks {
    pub(crate) fn new(full_compilation: bool) -> Self {
        FluxCallbacks { full_compilation }
    }
}

impl Callbacks for FluxCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        assert!(config.override_queries.is_none());

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

        queries.global_ctxt().unwrap().enter(|tcx| {
            if !is_tool_registered(tcx) {
                return;
            }
            let sess = FluxSession::new(&tcx.sess.opts, tcx.sess.parse_sess.clone_source_map());
            let _ = check_crate(tcx, &sess);
            sess.finish_diagnostics();
        });

        if self.full_compilation {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

fn check_crate(tcx: TyCtxt, sess: &FluxSession) -> Result<(), ErrorGuaranteed> {
    tracing::info_span!("check_crate").in_scope(|| {
        let cstore = CStore::load(tcx, sess);
        let mut specs = SpecCollector::collect(tcx, sess)?;

        // Ignore everything and go home
        if specs.ignores.contains(&IgnoreKey::Crate) {
            return Ok(());
        }

        // Do defn-expansion _after_ the WF check, so errors are given at user-specification level
        let mut early_cx = EarlyCtxt::new(tcx, sess, Box::new(cstore), fhir::Map::default());
        build_fhir_map(&mut early_cx, &mut specs)?;
        check_wf(&early_cx)?;

        tracing::info!("Callbacks::check_wf");

        let mut genv = GlobalEnv::new(early_cx)?;

        let mut ck = CrateChecker::new(&mut genv, specs.ignores);

        let crate_items = tcx.hir_crate_items(());
        let items = crate_items.items().map(|item| item.owner_id.def_id);
        let impl_items = crate_items
            .impl_items()
            .map(|impl_item| impl_item.owner_id.def_id);

        let result = items
            .chain(impl_items)
            .try_for_each_exhaust(|def_id| ck.check_def(def_id));

        ck.cache.save().unwrap_or(());

        tracing::info!("Callbacks::check_crate");

        save_metadata(&genv);

        result
    })
}

fn save_metadata(genv: &GlobalEnv) {
    let tcx = genv.tcx;
    if tcx
        .sess
        .opts
        .output_types
        .contains_key(&OutputType::Metadata)
    {
        let path = flux_metadata::filename_for_metadata(tcx);
        flux_metadata::encode_metadata(genv, path.as_path());
    }
}

struct CrateChecker<'a, 'genv, 'tcx> {
    genv: &'a mut GlobalEnv<'genv, 'tcx>,
    ignores: Ignores,
    cache: QueryCache,
}

impl<'a, 'genv, 'tcx> CrateChecker<'a, 'genv, 'tcx> {
    fn new(genv: &'a mut GlobalEnv<'genv, 'tcx>, ignores: Ignores) -> Self {
        CrateChecker { genv, ignores, cache: QueryCache::load() }
    }

    fn is_trusted(&self, def_id: LocalDefId) -> bool {
        self.genv.map().is_trusted(def_id)
    }

    /// `is_ignored` transitively follows the `def_id`'s parent-chain to check if
    /// any enclosing mod has been marked as `ignore`
    fn is_ignored(&self, def_id: LocalDefId) -> bool {
        let parent_def_id = self.genv.tcx.parent_module_from_def_id(def_id);
        if parent_def_id == def_id {
            false
        } else {
            self.ignores.contains(&IgnoreKey::Module(parent_def_id))
                || self.is_ignored(parent_def_id)
        }
    }

    fn matches_check_def(&self, def_id: LocalDefId) -> bool {
        let def_path = self.genv.tcx.def_path_str(def_id.to_def_id());
        def_path.contains(config::check_def())
    }

    fn check_def(&mut self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        if self.is_ignored(def_id) || !self.matches_check_def(def_id) {
            return Ok(());
        }

        match self.genv.tcx.def_kind(def_id.to_def_id()) {
            DefKind::Fn | DefKind::AssocFn => self.check_fn(def_id),
            DefKind::Enum => {
                let adt_def = self.genv.adt_def(def_id.to_def_id());
                let enum_def = self.genv.map().get_enum(def_id);
                refineck::invariants::check_invariants(
                    self.genv,
                    &mut self.cache,
                    &enum_def.invariants,
                    &adt_def,
                )
            }
            DefKind::Struct => {
                let adt_def = self.genv.adt_def(def_id.to_def_id());
                let struct_def = self.genv.map().get_struct(def_id);
                if struct_def.is_opaque() {
                    return Ok(());
                }
                refineck::invariants::check_invariants(
                    self.genv,
                    &mut self.cache,
                    &struct_def.invariants,
                    &adt_def,
                )
            }
            _ => Ok(()),
        }
    }

    fn check_fn(&mut self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        if self.is_trusted(def_id) {
            return Ok(());
        }

        let mir = unsafe { flux_common::mir_storage::retrieve_mir_body(self.genv.tcx, def_id) };

        // HACK(nilehmann) this will ignore any code generated by a macro. This is
        // a temporary workaround to allow `#[derive(PartialEq, Eq)]` and should be
        // removed.
        if mir.span.ctxt() > rustc_span::SyntaxContext::root() {
            return Ok(());
        }

        if config::dump_mir() {
            rustc_middle::mir::pretty::write_mir_fn(
                self.genv.tcx,
                &mir,
                &mut |_, _| Ok(()),
                &mut dbg::writer_for_item(self.genv.tcx, def_id.to_def_id(), "mir").unwrap(),
            )
            .unwrap();
        }

        let body =
            rustc::lowering::LoweringCtxt::lower_mir_body(self.genv.tcx, self.genv.sess, mir)?;

        refineck::check_fn(self.genv, &mut self.cache, def_id.to_def_id(), &body)
    }
}

fn build_fhir_map(early_cx: &mut EarlyCtxt, specs: &mut Specs) -> Result<(), ErrorGuaranteed> {
    let mut err: Option<ErrorGuaranteed> = None;

    // Register Generics
    err = defs_with_generics(early_cx.tcx)
        .try_for_each_exhaust(|def_id| {
            let generics = fhir::lift::lift_generics(early_cx, def_id)?;
            early_cx.map.insert_generics(def_id, generics);
            Ok(())
        })
        .err()
        .or(err);

    // Register Sorts
    for sort_decl in std::mem::take(&mut specs.sort_decls) {
        early_cx
            .map
            .insert_sort_decl(desugar::desugar_sort_decl(sort_decl));
    }

    // Register Consts
    for (def_id, const_sig) in std::mem::take(&mut specs.consts) {
        let did = def_id.to_def_id();
        let sym = def_id_symbol(early_cx.tcx, def_id);
        early_cx
            .map
            .insert_const(ConstInfo { def_id: did, sym, val: const_sig.val });
    }

    // Register UIFs
    err = std::mem::take(&mut specs.uifs)
        .into_iter()
        .try_for_each_exhaust(|uif_def| {
            let name = uif_def.name;
            let uif_def = desugar::resolve_uif_def(early_cx, uif_def)?;
            early_cx.map.insert_uif(name.name, uif_def);
            Ok(())
        })
        .err()
        .or(err);

    // Register Defns as UIFs for sort-checking
    err = specs
        .dfns
        .iter()
        .try_for_each_exhaust(|defn| {
            let name = defn.name;
            let defn_uif = desugar::resolve_defn_uif(early_cx, defn)?;
            early_cx.map.insert_uif(name.name, defn_uif);
            Ok(())
        })
        .err()
        .or(err);

    // Register AdtDefs
    err = specs
        .structs
        .iter()
        .try_for_each_exhaust(|(def_id, def)| {
            let refined_by = def.refined_by.as_ref().unwrap_or(surface::RefinedBy::DUMMY);
            let adt_def = desugar::desugar_refined_by(early_cx, *def_id, refined_by)?;
            early_cx.map.insert_refined_by(*def_id, adt_def);
            Ok(())
        })
        .err()
        .or(err);
    err = specs
        .enums
        .iter()
        .try_for_each_exhaust(|(def_id, def)| {
            let refined_by = def.refined_by.as_ref().unwrap_or(surface::RefinedBy::DUMMY);
            let adt_def = desugar::desugar_refined_by(early_cx, *def_id, refined_by)?;
            early_cx.map.insert_refined_by(*def_id, adt_def);
            Ok(())
        })
        .err()
        .or(err);
    err = specs
        .aliases
        .iter()
        .try_for_each_exhaust(|(def_id, alias)| {
            let adt_def = if let Some(alias) = alias {
                desugar::desugar_refined_by(early_cx, *def_id, &alias.refined_by)?
            } else {
                fhir::lift::lift_refined_by(early_cx, *def_id)
            };
            early_cx.map.insert_refined_by(*def_id, adt_def);
            Ok(())
        })
        .err()
        .or(err);

    // Desugaring after this depends on the `fhir::Map` containing the information
    // collected before, so we bail out if there's any error at this point.
    if let Some(err) = err {
        return Err(err);
    }

    // Register Defns
    err = std::mem::take(&mut specs.dfns)
        .into_iter()
        .try_for_each_exhaust(|defn| {
            let name = defn.name;
            let defn = desugar::desugar_defn(early_cx, defn)?;
            early_cx.map.insert_defn(name.name, defn);
            Ok(())
        })
        .err()
        .or(err);

    // Qualifiers
    err = specs
        .qualifs
        .iter()
        .try_for_each_exhaust(|qualifier| {
            let qualifier = desugar::desugar_qualifier(early_cx, qualifier)?;
            early_cx.map.insert_qualifier(qualifier);
            Ok(())
        })
        .err()
        .or(err);

    // Aliases
    err = std::mem::take(&mut specs.aliases)
        .into_iter()
        .try_for_each_exhaust(|(def_id, alias)| {
            let alias = if let Some(alias) = alias {
                desugar::desugar_type_alias(early_cx, def_id, alias)?
            } else {
                fhir::lift::lift_type_alias(early_cx, def_id)?
            };
            early_cx.map.insert_type_alias(def_id, alias);
            Ok(())
        })
        .err()
        .or(err);

    // Structs
    err = std::mem::take(&mut specs.structs)
        .into_iter()
        .try_for_each_exhaust(|(def_id, struct_def)| {
            let struct_def = desugar::desugar_struct_def(early_cx, struct_def)?;
            if config::dump_fhir() {
                dbg::dump_item_info(early_cx.tcx, def_id, "fhir", &struct_def).unwrap();
            }
            early_cx.map.insert_struct(def_id, struct_def);
            Ok(())
        })
        .err()
        .or(err);

    // Enums
    err = std::mem::take(&mut specs.enums)
        .into_iter()
        .try_for_each_exhaust(|(def_id, enum_def)| {
            early_cx
                .map
                .insert_enum(def_id, desugar::desugar_enum_def(early_cx, enum_def)?);
            Ok(())
        })
        .err()
        .or(err);

    // FnSigs
    err = std::mem::take(&mut specs.fns)
        .into_iter()
        .try_for_each_exhaust(|(def_id, spec)| {
            if spec.trusted {
                early_cx.map.add_trusted(def_id);
            }
            let fn_sig = if let Some(fn_sig) = spec.fn_sig {
                desugar::desugar_fn_sig(early_cx, def_id, fn_sig)?
            } else {
                fhir::lift::lift_fn_sig(early_cx, def_id)?
            };
            if config::dump_fhir() {
                dbg::dump_item_info(early_cx.tcx, def_id.to_def_id(), "fhir", &fn_sig).unwrap();
            }
            early_cx.map.insert_fn_sig(def_id, fn_sig);
            if let Some(quals) = spec.qual_names {
                early_cx.map.insert_fn_quals(def_id, quals.names);
            }
            Ok(())
        })
        .err()
        .or(err);

    if let Some(err) = err {
        Err(err)
    } else {
        Ok(())
    }
}

fn check_wf(early_cx: &EarlyCtxt) -> Result<(), ErrorGuaranteed> {
    let mut err: Option<ErrorGuaranteed> = None;

    for defn in early_cx.map.defns() {
        err = Wf::check_defn(early_cx, defn).err().or(err);
    }

    for qualifier in early_cx.map.qualifiers() {
        err = Wf::check_qualifier(early_cx, qualifier).err().or(err);
    }

    for alias in early_cx.map.type_aliases() {
        err = Wf::check_alias(early_cx, alias).err().or(err);
    }

    for struct_def in early_cx.map.structs() {
        err = Wf::check_struct_def(early_cx, struct_def).err().or(err);
    }

    for enum_def in early_cx.map.enums() {
        err = Wf::check_enum_def(early_cx, enum_def).err().or(err);
    }

    for (def_id, fn_sig) in early_cx.map.fn_sigs() {
        err = annot_check::check_fn_sig(early_cx, def_id, fn_sig)
            .err()
            .or(err);
        err = Wf::check_fn_sig(early_cx, fn_sig).err().or(err);
    }

    let qualifiers = early_cx.map.qualifiers().map(|q| q.name.clone()).collect();
    for (_, fn_quals) in early_cx.map.fn_quals() {
        err = Wf::check_fn_quals(early_cx.sess, &qualifiers, fn_quals)
            .err()
            .or(err);
    }

    if let Some(err) = err {
        Err(err)
    } else {
        Ok(())
    }
}

fn def_id_symbol(tcx: TyCtxt, def_id: LocalDefId) -> rustc_span::Symbol {
    let did = def_id.to_def_id();
    // TODO(RJ) use fully qualified names: Symbol::intern(&tcx.def_path_str(did))
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
        flux_common::mir_storage::store_mir_body(tcx, def_id, body_with_facts);
    }
    let mut providers = Providers::default();
    rustc_borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn is_tool_registered(tcx: TyCtxt) -> bool {
    for attr in tcx.hir().krate_attrs() {
        if rustc_ast_pretty::pprust::attribute_to_string(attr) == "#![register_tool(flux)]" {
            return true;
        }
    }
    false
}

fn defs_with_generics(tcx: TyCtxt) -> impl Iterator<Item = LocalDefId> + '_ {
    tcx.hir_crate_items(())
        .definitions()
        .flat_map(move |def_id| {
            match tcx.def_kind(def_id) {
                DefKind::Struct
                | DefKind::Enum
                | DefKind::Fn
                | DefKind::Impl { .. }
                | DefKind::TyAlias
                | DefKind::AssocFn => Some(def_id),
                _ => None,
            }
        })
}
