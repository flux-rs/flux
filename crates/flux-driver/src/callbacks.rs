use flux_common::{cache::QueryCache, dbg, iter::IterExt, result::ResultExt};
use flux_config as config;
use flux_errors::FluxSession;
use flux_fhir_analysis::compare_impl_item;
use flux_metadata::CStore;
use flux_middle::{fhir, global_env::GlobalEnv, queries::Providers, Specs};
use flux_refineck as refineck;
use refineck::CheckerConfig;
use rustc_borrowck::consumers::ConsumerOptions;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::{query, ty::TyCtxt};
use rustc_session::config::OutputType;

use crate::{collector::SpecCollector, DEFAULT_LOCALE_RESOURCES};

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
        if compiler.sess.dcx().has_errors().is_some() {
            return;
        }

        queries.global_ctxt().unwrap().enter(|tcx| {
            let sess = FluxSession::new(
                &tcx.sess.opts,
                tcx.sess.psess.clone_source_map(),
                rustc_errors::fallback_fluent_bundle(DEFAULT_LOCALE_RESOURCES.to_vec(), false),
            );

            let mut providers = Providers::default();
            flux_desugar::provide(&mut providers);
            flux_fhir_analysis::provide(&mut providers);
            providers.collect_specs = collect_specs;

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
        tracing::info!("Callbacks::check_wf");

        let fhir = genv.fhir_crate();

        // Ignore everything and go home
        if fhir.ignores.contains(&fhir::IgnoreKey::Crate) {
            return Ok(());
        }
        flux_fhir_analysis::check_crate_wf(genv)?;
        let mut ck = CrateChecker::new(genv, fhir);

        let crate_items = genv.tcx().hir_crate_items(());

        let result = crate_items
            .definitions()
            .try_for_each_exhaust(|def_id| ck.check_def(def_id));

        ck.cache.save().unwrap_or(());

        tracing::info!("Callbacks::check_crate");
        save_metadata(&genv);

        result
    })
}

fn collect_specs(genv: GlobalEnv) -> Specs {
    match SpecCollector::collect(genv.tcx(), genv.sess()) {
        Ok(specs) => specs,
        Err(err) => {
            genv.sess().abort(err);
        }
    }
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
    fhir: &'genv fhir::Crate<'genv>,
    cache: QueryCache,
    checker_config: CheckerConfig,
}

impl<'genv, 'tcx> CrateChecker<'genv, 'tcx> {
    fn new(genv: GlobalEnv<'genv, 'tcx>, fhir: &'genv fhir::Crate<'genv>) -> Self {
        let checker_config = CheckerConfig {
            check_overflow: fhir.crate_config.check_overflow,
            scrape_quals: fhir.crate_config.scrape_quals,
        };
        CrateChecker { genv, fhir, cache: QueryCache::load(), checker_config }
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
            self.fhir
                .ignores
                .contains(&fhir::IgnoreKey::Module(parent_def_id))
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

        match self.genv.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                // Skip trait methods without body
                if self
                    .genv
                    .tcx()
                    .hir_node_by_def_id(def_id)
                    .body_id()
                    .is_some()
                {
                    refineck::check_fn(self.genv, &mut self.cache, def_id, self.checker_config)?;
                }
                Ok(())
            }
            DefKind::Enum => {
                let adt_def = self.genv.adt_def(def_id.to_def_id()).emit(&self.genv)?;
                let enum_def = self
                    .genv
                    .map()
                    .expect_item(def_id)
                    .emit(&self.genv)?
                    .expect_enum();
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
                let adt_def = self.genv.adt_def(def_id.to_def_id()).emit(&self.genv)?;
                let struct_def = self
                    .genv
                    .map()
                    .expect_item(def_id)
                    .emit(&self.genv)?
                    .expect_struct();
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
