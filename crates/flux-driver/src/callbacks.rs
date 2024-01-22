use config::CrateConfig;
use desugar::resolver::{Resolver, ResolverOutput};
use flux_common::{cache::QueryCache, dbg, iter::IterExt};
use flux_config as config;
use flux_desugar as desugar;
use flux_errors::{FluxSession, ResultExt};
use flux_fhir_analysis::compare_impl_item;
use flux_metadata::CStore;
use flux_middle::{
    fhir::{self, lift, ConstInfo},
    global_env::GlobalEnv,
    queries::Providers,
};
use flux_refineck as refineck;
use refineck::CheckerConfig;
use rustc_borrowck::consumers::ConsumerOptions;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{self as hir, def::DefKind, def_id::LocalDefId, OwnerId};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::{query, ty::TyCtxt};
use rustc_session::config::OutputType;
use rustc_span::Symbol;

use crate::{
    collector::{IgnoreKey, Ignores, SpecCollector, Specs},
    DEFAULT_LOCALE_RESOURCES,
};

#[derive(Default)]
pub struct FluxCallbacks {
    pub full_compilation: bool,
    pub verify: bool,
}

impl Callbacks for FluxCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        assert!(config.override_queries.is_none());

        config.override_queries = Some(|_, local| {
            local.mir_borrowck = mir_borrowck;
        });
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        if self.verify {
            self.verify(compiler, queries);
        }

        if self.full_compilation {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

impl FluxCallbacks {
    fn verify<'tcx>(&self, compiler: &Compiler, queries: &'tcx Queries<'tcx>) {
        if compiler
            .session()
            .diagnostic()
            .has_errors_or_lint_errors()
            .is_some()
        {
            return;
        }

        queries.global_ctxt().unwrap().enter(|tcx| {
            let sess = FluxSession::new(
                &tcx.sess.opts,
                tcx.sess.parse_sess.clone_source_map(),
                rustc_errors::fallback_fluent_bundle(DEFAULT_LOCALE_RESOURCES.to_vec(), false),
            );

            let mut providers = Providers::default();
            flux_fhir_analysis::provide(&mut providers);

            let cstore = CStore::load(tcx, &sess);
            let arena = fhir::Arena::new();
            GlobalEnv::enter(tcx, &sess, Box::new(cstore), &arena, providers, |genv| {
                let _ = check_crate(genv);
            });
            sess.finish_diagnostics();
        });
    }
}

fn check_crate(genv: GlobalEnv) -> Result<(), ErrorGuaranteed> {
    tracing::info_span!("check_crate").in_scope(move || {
        let specs = SpecCollector::collect(genv.tcx(), genv.sess())?;

        // Ignore everything and go home
        if specs.ignores.contains(&IgnoreKey::Crate) {
            return Ok(());
        }

        let resolver_output = resolve_crate(genv, &specs)?;
        desugar_crate(genv, &specs, &resolver_output)?;

        flux_fhir_analysis::check_crate_wf(genv)?;

        tracing::info!("Callbacks::check_wf");

        let mut ck = CrateChecker::new(genv, specs.ignores, specs.crate_config);

        let crate_items = genv.tcx().hir_crate_items(());
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

fn collect_global_items(tcx: TyCtxt, resolver_output: &mut ResolverOutput, specs: &Specs) {
    for sort_decl in &specs.sort_decls {
        resolver_output
            .sort_decls
            .insert(sort_decl.name.name, desugar::desugar_sort_decl(sort_decl));
    }

    for def_id in specs.consts.keys() {
        let did = def_id.to_def_id();
        let sym = def_id_symbol(tcx, *def_id);
        resolver_output.consts.insert(sym, did);
    }

    for defn in &specs.func_defs {
        let kind = if defn.body.is_some() { fhir::FuncKind::Def } else { fhir::FuncKind::Uif };
        resolver_output.func_decls.insert(defn.name.name, kind);
    }

    for itf in flux_middle::theory_funcs() {
        resolver_output
            .func_decls
            .insert(itf.name, fhir::FuncKind::Thy(itf.fixpoint_name));
    }
}

fn resolve_crate(genv: GlobalEnv, specs: &Specs) -> Result<ResolverOutput, ErrorGuaranteed> {
    let mut resolver = Resolver::new(genv.tcx(), genv.sess());
    genv.tcx()
        .hir_crate_items(())
        .owners()
        .try_for_each_exhaust(|id| {
            match genv.tcx().def_kind(id) {
                DefKind::Struct => resolver.resolve_struct_def(id, &specs.structs[&id])?,
                DefKind::Enum => resolver.resolve_enum_def(id, &specs.enums[&id])?,
                DefKind::TyAlias { .. } => {
                    if let Some(type_alias) = &specs.ty_aliases[&id] {
                        resolver.resolve_type_alias(id, type_alias)?;
                    }
                }
                DefKind::Fn | DefKind::AssocFn => {
                    if let Some(fn_sig) = specs.fn_sigs[&id].fn_sig.as_ref() {
                        resolver.resolve_fn_sig(id, fn_sig)?;
                    }
                }
                _ => {}
            }
            Ok(())
        })?;
    let mut resolver_output = resolver.into_output();

    collect_global_items(genv.tcx(), &mut resolver_output, specs);

    Ok(resolver_output)
}

fn desugar_crate(
    genv: GlobalEnv,
    specs: &Specs,
    resolver_output: &ResolverOutput,
) -> Result<(), ErrorGuaranteed> {
    let mut err: Option<ErrorGuaranteed> = None;

    for defn in &specs.func_defs {
        let name = defn.name;
        let func_decl = desugar::func_def_to_func_decl(genv, resolver_output, defn)?;
        genv.map().insert_func_decl(name.name, func_decl);
    }

    for (def_id, const_sig) in &specs.consts {
        let did = def_id.to_def_id();
        let sym = def_id_symbol(genv.tcx(), *def_id);
        genv.map()
            .insert_const(ConstInfo { def_id: did, sym, val: const_sig.val });
    }

    // Defns
    err = specs
        .func_defs
        .iter()
        .try_for_each_exhaust(|defn| {
            let name = defn.name;
            if let Some(defn) = desugar::desugar_defn(genv, resolver_output, defn)? {
                genv.map().insert_defn(name.name, defn);
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
            let qualifier = desugar::desugar_qualifier(genv, resolver_output, qualifier)?;
            genv.map().insert_qualifier(qualifier);
            Ok(())
        })
        .err()
        .or(err);

    err = genv
        .tcx()
        .hir_crate_items(())
        .items()
        .try_for_each_exhaust(|item_id| desugar_item(genv, specs, item_id, resolver_output))
        .err()
        .or(err);

    specs
        .extern_specs
        .iter()
        .for_each(|(extern_def_id, local_def_id)| {
            genv.map().insert_extern(*extern_def_id, *local_def_id);
        });

    if let Some(err) = err {
        Err(err)
    } else {
        Ok(())
    }
}

fn desugar_item(
    genv: GlobalEnv,
    specs: &Specs,
    item_id: hir::ItemId,
    resolver_output: &ResolverOutput,
) -> Result<(), ErrorGuaranteed> {
    let owner_id = item_id.owner_id;
    let item = genv.hir().item(item_id);

    match item.kind {
        hir::ItemKind::Fn(..) => {
            desugar_fn_sig(genv, specs, owner_id, resolver_output)?;
        }
        hir::ItemKind::TyAlias(..) => {
            let ty_alias = specs.ty_aliases[&owner_id].as_ref();
            desugar::desugar_type_alias(genv, owner_id, ty_alias, resolver_output)?;
        }
        hir::ItemKind::OpaqueTy(_) => {
            // Opaque types are desugared as part of the desugaring of their defining function
        }
        hir::ItemKind::Enum(..) => {
            let enum_def = &specs.enums[&owner_id];
            desugar::desugar_enum_def(genv, owner_id, enum_def, resolver_output)?;
        }
        hir::ItemKind::Struct(..) => {
            let struct_def = &specs.structs[&owner_id];
            desugar::desugar_struct_def(genv, owner_id, struct_def, resolver_output)?;
        }
        hir::ItemKind::Trait(.., items) => {
            desugar::desugar_trait(genv, owner_id, resolver_output, &specs.traits[&owner_id])?;
            items.iter().try_for_each_exhaust(|trait_item| {
                desugar_assoc_item(
                    genv,
                    specs,
                    trait_item.id.owner_id,
                    trait_item.kind,
                    resolver_output,
                )
            })?;
        }
        hir::ItemKind::Impl(impl_) => {
            desugar::desugar_impl(genv, owner_id, resolver_output, &specs.impls[&owner_id])?;
            impl_.items.iter().try_for_each_exhaust(|impl_item| {
                desugar_assoc_item(
                    genv,
                    specs,
                    impl_item.id.owner_id,
                    impl_item.kind,
                    resolver_output,
                )
            })?;
        }
        _ => {}
    }
    Ok(())
}

fn desugar_assoc_item(
    genv: GlobalEnv,
    specs: &Specs,
    owner_id: OwnerId,
    kind: hir::AssocItemKind,
    resolver_output: &ResolverOutput,
) -> Result<(), ErrorGuaranteed> {
    match kind {
        hir::AssocItemKind::Fn { .. } => desugar_fn_sig(genv, specs, owner_id, resolver_output),
        hir::AssocItemKind::Type => {
            let generics = lift::lift_generics(genv, owner_id)?;
            let assoc_ty = fhir::AssocType { generics };
            genv.map().insert_assoc_type(owner_id.def_id, assoc_ty);
            Ok(())
        }
        hir::AssocItemKind::Const => Ok(()),
    }
}

fn desugar_fn_sig(
    genv: GlobalEnv,
    specs: &Specs,
    owner_id: OwnerId,
    resolver_output: &ResolverOutput,
) -> Result<(), ErrorGuaranteed> {
    let spec = specs.fn_sigs.get(&owner_id).unwrap();
    let def_id = owner_id.def_id;
    if spec.trusted {
        genv.map().add_trusted(def_id);
    }

    desugar::desugar_fn_sig(genv, owner_id, spec.fn_sig.as_ref(), resolver_output)?;

    if let Some(quals) = &spec.qual_names {
        genv.map().insert_fn_quals(def_id, &quals.names);
    }
    Ok(())
}

fn save_metadata(genv: &GlobalEnv) {
    let tcx = genv.tcx();
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

struct CrateChecker<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    ignores: Ignores,
    cache: QueryCache,
    checker_config: CheckerConfig,
}

impl<'genv, 'tcx> CrateChecker<'genv, 'tcx> {
    fn new(
        genv: GlobalEnv<'genv, 'tcx>,
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
        let parent_def_id = self
            .genv
            .tcx()
            .parent_module_from_def_id(def_id)
            .to_local_def_id();
        if parent_def_id == def_id {
            false
        } else {
            self.ignores.contains(&IgnoreKey::Module(parent_def_id))
                || self.is_ignored(parent_def_id)
        }
    }

    fn matches_check_def(&self, def_id: LocalDefId) -> bool {
        let def_path = self.genv.tcx().def_path_str(def_id.to_def_id());
        def_path.contains(config::check_def())
    }

    fn check_def(&mut self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        if self.is_ignored(def_id) || !self.matches_check_def(def_id) {
            return Ok(());
        }

        match self.genv.tcx().def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                refineck::check_fn(self.genv, &mut self.cache, def_id, self.checker_config)
            }
            DefKind::Enum => {
                let adt_def = self
                    .genv
                    .adt_def(def_id.to_def_id())
                    .emit(self.genv.sess())?;
                let enum_def = self.genv.map().expect_enum(def_id);
                refineck::invariants::check_invariants(
                    self.genv,
                    &mut self.cache,
                    def_id,
                    enum_def.invariants,
                    &adt_def,
                    self.checker_config,
                )
            }
            DefKind::Struct => {
                let adt_def = self
                    .genv
                    .adt_def(def_id.to_def_id())
                    .emit(self.genv.sess())?;
                let struct_def = self.genv.map().expect_struct(def_id);
                if struct_def.is_opaque() {
                    return Ok(());
                }
                refineck::invariants::check_invariants(
                    self.genv,
                    &mut self.cache,
                    def_id,
                    struct_def.invariants,
                    &adt_def,
                    self.checker_config,
                )
            }
            DefKind::Impl { of_trait } => {
                if of_trait {
                    compare_impl_item::check_impl_against_trait(self.genv, def_id)?;
                }
                Ok(())
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
