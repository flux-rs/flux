use config::CrateConfig;
use flux_common::{cache::QueryCache, dbg, iter::IterExt};
use flux_config as config;
use flux_desugar as desugar;
use flux_errors::{FluxSession, ResultExt};
use flux_metadata::CStore;
use flux_middle::{
    early_ctxt::EarlyCtxt,
    fhir::{self, ConstInfo},
    global_env::GlobalEnv,
};
use flux_refineck as refineck;
use refineck::CheckerConfig;
use rustc_borrowck::consumers::ConsumerOptions;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{def::DefKind, def_id::LocalDefId, OwnerId};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::{query, ty::TyCtxt};
use rustc_session::{config::OutputType, EarlyErrorHandler};

use crate::{
    collector::{IgnoreKey, Ignores, SpecCollector, Specs},
    DEFAULT_LOCALE_RESOURCES,
};

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
        _handler: &EarlyErrorHandler,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        if compiler
            .session()
            .diagnostic()
            .has_errors_or_lint_errors()
            .is_some()
        {
            return Compilation::Stop;
        }

        queries.global_ctxt().unwrap().enter(|tcx| {
            if !is_tool_registered(tcx) {
                return;
            }
            let sess = FluxSession::new(
                &tcx.sess.opts,
                tcx.sess.parse_sess.clone_source_map(),
                rustc_errors::fallback_fluent_bundle(DEFAULT_LOCALE_RESOURCES.to_vec(), false),
            );
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

        let map = build_stage1_fhir_map(tcx, sess, &mut specs)?;
        let early_cx = build_stage2_fhir_map(tcx, sess, map, cstore, &mut specs)?;

        let func_decls = flux_fhir_analysis::conv_func_decls(&early_cx);
        let mut genv = GlobalEnv::new(early_cx, func_decls);
        flux_fhir_analysis::provide(genv.providers());

        flux_fhir_analysis::check_crate_wf(&genv)?;

        tracing::info!("Callbacks::check_wf");

        let mut ck = CrateChecker::new(&mut genv, specs.ignores, specs.crate_config);

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

fn build_stage1_fhir_map(
    tcx: TyCtxt,
    sess: &FluxSession,
    specs: &mut Specs,
) -> Result<fhir::Map, ErrorGuaranteed> {
    let mut err: Option<ErrorGuaranteed> = None;

    let mut map = fhir::Map::new();

    // Register Sorts
    for sort_decl in std::mem::take(&mut specs.sort_decls) {
        map.insert_sort_decl(desugar::desugar_sort_decl(sort_decl));
    }

    // Register Generics and Predicates
    err = defs_with_generics(tcx)
        .try_for_each_exhaust(|owner_id| {
            let generics = fhir::lift::lift_generics(tcx, sess, owner_id)?;
            map.insert_generics(owner_id.def_id, generics);
            Ok(())
        })
        .err()
        .or(err);

    // Register Consts
    for (def_id, const_sig) in std::mem::take(&mut specs.consts) {
        let did = def_id.to_def_id();
        let sym = def_id_symbol(tcx, def_id);
        map.insert_const(ConstInfo { def_id: did, sym, val: const_sig.val });
    }

    // Register FnDecls
    err = specs
        .func_defs
        .iter()
        .try_for_each_exhaust(|defn| {
            let name = defn.name;
            let func_decl = desugar::func_def_to_func_decl(sess, map.sort_decls(), defn)?;
            map.insert_func_decl(name.name, func_decl);
            Ok(())
        })
        .err()
        .or(err);

    // Register RefinedBys
    err = specs
        .refined_bys()
        .try_for_each_exhaust(|(owner_id, refined_by)| {
            let refined_by = if let Some(refined_by) = refined_by {
                desugar::desugar_refined_by(sess, map.sort_decls(), owner_id, refined_by)?
            } else {
                fhir::lift::lift_refined_by(tcx, owner_id)
            };
            map.insert_refined_by(owner_id.def_id, refined_by);
            Ok(())
        })
        .err()
        .or(err);

    // Externs
    std::mem::take(&mut specs.extern_specs)
        .into_iter()
        .for_each(|(extern_def_id, local_def_id)| {
            map.insert_extern(extern_def_id, local_def_id);
        });

    if let Some(err) = err {
        Err(err)
    } else {
        Ok(map)
    }
}

fn build_stage2_fhir_map<'sess, 'tcx>(
    tcx: TyCtxt<'tcx>,
    sess: &'sess FluxSession,
    map: fhir::Map,
    cstore: CStore,
    specs: &mut Specs,
) -> Result<EarlyCtxt<'sess, 'tcx>, ErrorGuaranteed> {
    let mut err: Option<ErrorGuaranteed> = None;
    let mut early_cx = EarlyCtxt::new(tcx, sess, Box::new(cstore), map);

    // Register Defns
    err = std::mem::take(&mut specs.func_defs)
        .into_iter()
        .try_for_each_exhaust(|defn| {
            let name = defn.name;
            if let Some(defn) = desugar::desugar_defn(&early_cx, defn)? {
                early_cx.map.insert_defn(name.name, defn);
            }
            Ok(())
        })
        .err()
        .or(err);

    // Qualifiers
    err = specs
        .qualifs
        .iter()
        .try_for_each_exhaust(|qualifier| {
            let qualifier = desugar::desugar_qualifier(&early_cx, qualifier)?;
            early_cx.map.insert_qualifier(qualifier);
            Ok(())
        })
        .err()
        .or(err);

    // Aliases
    err = std::mem::take(&mut specs.aliases)
        .into_iter()
        .try_for_each_exhaust(|(owner_id, alias)| {
            let alias = if let Some(alias) = alias {
                desugar::desugar_type_alias(&early_cx, owner_id, alias)?
            } else {
                fhir::lift::lift_type_alias(tcx, sess, owner_id)?
            };
            early_cx.map.insert_type_alias(owner_id.def_id, alias);
            Ok(())
        })
        .err()
        .or(err);

    // Structs
    err = std::mem::take(&mut specs.structs)
        .into_iter()
        .try_for_each_exhaust(|(owner_id, struct_def)| {
            let struct_def = desugar::desugar_struct_def(&early_cx, owner_id, struct_def)?;
            if config::dump_fhir() {
                dbg::dump_item_info(tcx, owner_id, "fhir", &struct_def).unwrap();
            }
            early_cx.map.insert_struct(owner_id.def_id, struct_def);
            Ok(())
        })
        .err()
        .or(err);

    // Enums
    err = std::mem::take(&mut specs.enums)
        .into_iter()
        .try_for_each_exhaust(|(owner_id, enum_def)| {
            let enum_def = desugar::desugar_enum_def(&early_cx, owner_id, enum_def)?;
            if config::dump_fhir() {
                dbg::dump_item_info(tcx, owner_id.to_def_id(), "fhir", &enum_def).unwrap();
            }
            early_cx.map.insert_enum(owner_id.def_id, enum_def);
            Ok(())
        })
        .err()
        .or(err);

    // FnSigs
    err = std::mem::take(&mut specs.fn_sigs)
        .into_iter()
        .try_for_each_exhaust(|(owner_id, spec)| {
            let def_id = owner_id.def_id;
            if spec.trusted {
                early_cx.map.add_trusted(def_id);
            }
            let (fn_sig, fn_preds) = if let Some(fn_sig) = spec.fn_sig {
                let (fhir_fn_sig, fhir_fn_preds, fhir_opaque_impls) =
                    desugar::desugar_fn_sig(&early_cx, owner_id, fn_sig)?;
                (fhir_fn_sig, Some((fhir_fn_preds, fhir_opaque_impls)))
            } else {
                (fhir::lift::lift_fn_sig(tcx, sess, owner_id)?, None)
            };
            if config::dump_fhir() {
                dbg::dump_item_info(tcx, def_id, "fhir", &fn_sig).unwrap();
            }
            early_cx.map.insert_fn_sig(def_id, fn_sig);
            if let Some((preds, item_bounds)) = fn_preds {
                early_cx.map.insert_predicates(def_id, preds);
                for (def_id, predicates) in item_bounds {
                    early_cx.map.insert_item_bounds(def_id, predicates)
                }
            }
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
        Ok(early_cx)
    }
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
    checker_config: CheckerConfig,
}

impl<'a, 'genv, 'tcx> CrateChecker<'a, 'genv, 'tcx> {
    fn new(
        genv: &'a mut GlobalEnv<'genv, 'tcx>,
        ignores: Ignores,
        crate_config: Option<CrateConfig>,
    ) -> Self {
        let crate_config = crate_config.unwrap_or_default();
        let checker_config = CheckerConfig {
            check_overflow: crate_config.check_overflow,
            scrape_quals: crate_config.scrape_quals,
        };
        CrateChecker { genv, ignores, cache: QueryCache::load(), checker_config }
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

        match self.genv.tcx.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                refineck::check_fn(self.genv, &mut self.cache, def_id, self.checker_config)
            }
            DefKind::Enum => {
                let adt_def = self.genv.adt_def(def_id.to_def_id()).emit(self.genv.sess)?;
                let enum_def = self.genv.map().get_enum(def_id);
                refineck::invariants::check_invariants(
                    self.genv,
                    &mut self.cache,
                    &enum_def.invariants,
                    &adt_def,
                    self.checker_config,
                )
            }
            DefKind::Struct => {
                let adt_def = self.genv.adt_def(def_id.to_def_id()).emit(self.genv.sess)?;
                let struct_def = self.genv.map().get_struct(def_id);
                if struct_def.is_opaque() {
                    return Ok(());
                }
                refineck::invariants::check_invariants(
                    self.genv,
                    &mut self.cache,
                    &struct_def.invariants,
                    &adt_def,
                    self.checker_config,
                )
            }
            _ => Ok(()),
        }
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
fn mir_borrowck<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> query::queries::mir_borrowck::ProvidedValue {
    let body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
        tcx,
        def_id,
        ConsumerOptions::RegionInferenceContext,
    );

    if config::dump_mir() {
        rustc_middle::mir::pretty::write_mir_fn(
            tcx,
            &body_with_facts.body,
            &mut |_, _| Ok(()),
            &mut dbg::writer_for_item(tcx, def_id.to_def_id(), "mir").unwrap(),
        )
        .unwrap();
    }

    // SAFETY: This is safe because we are feeding in the same `tcx` that is
    // going to be used as a witness when pulling out the data.
    unsafe {
        flux_common::mir_storage::store_mir_body(tcx, def_id, body_with_facts);
    }
    let mut providers = query::Providers::default();
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

fn defs_with_generics(tcx: TyCtxt) -> impl Iterator<Item = OwnerId> + '_ {
    tcx.hir_crate_items(())
        .definitions()
        .flat_map(move |def_id| {
            match tcx.def_kind(def_id) {
                DefKind::Struct
                | DefKind::Enum
                | DefKind::Fn
                | DefKind::Impl { .. }
                | DefKind::TyAlias
                | DefKind::AssocFn => Some(OwnerId { def_id }),
                _ => None,
            }
        })
}
