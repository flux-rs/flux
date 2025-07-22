use flux_common::{bug, cache::QueryCache, dbg, iter::IterExt, result::ResultExt};
use flux_config as config;
use flux_errors::FluxSession;
use flux_infer::fixpoint_encoding::FixQueryCache;
use flux_metadata::CStore;
use flux_middle::{
    Specs, fhir,
    global_env::GlobalEnv,
    queries::{Providers, QueryResult},
    timings,
};
use flux_refineck as refineck;
use itertools::Itertools;
use rustc_borrowck::consumers::ConsumerOptions;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE, LocalDefId},
};
use rustc_interface::interface::Compiler;
use rustc_middle::{query, ty::TyCtxt};
use rustc_session::config::OutputType;
use rustc_span::FileName;

use crate::{DEFAULT_LOCALE_RESOURCES, collector::SpecCollector};

#[derive(Default)]
pub struct FluxCallbacks;

impl Callbacks for FluxCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        assert!(config.override_queries.is_none());

        config.override_queries = Some(|_, local| {
            local.mir_borrowck = mir_borrowck;
        });
        // this should always be empty otherwise something changed in rustc and all our assumptions
        // about symbol interning are wrong.
        assert!(config.extra_symbols.is_empty());
        config.extra_symbols = flux_syntax::symbols::PREDEFINED_FLUX_SYMBOLS.to_vec();
    }

    fn after_analysis(&mut self, compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        self.verify(compiler, tcx);
        if config::full_compilation() { Compilation::Continue } else { Compilation::Stop }
    }
}

impl FluxCallbacks {
    fn verify(&self, compiler: &Compiler, tcx: TyCtxt<'_>) {
        if compiler.sess.dcx().has_errors().is_some() {
            return;
        }

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
            let result = timings::enter(tcx, || check_crate(genv));
            if result.is_ok() {
                encode_and_save_metadata(genv);
            }
        });
        sess.finish_diagnostics();
    }
}

fn check_crate(genv: GlobalEnv) -> Result<(), ErrorGuaranteed> {
    tracing::info_span!("check_crate").in_scope(move || {
        tracing::info!("Callbacks::check_wf");

        // Query qualifiers and spec funcs to report wf errors
        let _ = genv.qualifiers().emit(&genv)?;
        let _ = genv.normalized_defns(LOCAL_CRATE);

        let mut ck = CrateChecker::new(genv);

        let crate_items = genv.tcx().hir_crate_items(());

        let dups = crate_items.definitions().duplicates().collect_vec();
        if !dups.is_empty() {
            bug!("TODO: {dups:#?}");
        }
        let result = crate_items
            .definitions()
            .try_for_each_exhaust(|def_id| ck.check_def_catching_bugs(def_id));

        ck.cache.save().unwrap_or(());

        tracing::info!("Callbacks::check_crate");

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

fn encode_and_save_metadata(genv: GlobalEnv) {
    // HACK(nilehmann) do not encode metadata for `core`, this is so verify-rust-std works even
    // if it has unsupported items. We report errors lazily so partially analyzing the crate should
    // skip the error, except that encoding the metadata for the crate will trigger conversion for
    // all items which can trigger the error even if not included for analysis. To fix this properly
    // we should consider how to handle metadata encoding if only part of the crate is included for
    // analysis.
    if genv.tcx().crate_name(LOCAL_CRATE) == flux_syntax::symbols::sym::core {
        return;
    }

    // We only save metadata when `--emit=metadata` is passed as an argument. In this case, we save
    // the `.fluxmeta` file alongside the `.rmeta` file. This setup works for `cargo flux`, which
    // wraps `cargo check` and always passes `--emit=metadata`. Tests also explicitly pass this flag.
    let tcx = genv.tcx();
    if tcx
        .output_filenames(())
        .outputs
        .contains_key(&OutputType::Metadata)
    {
        let path = flux_metadata::filename_for_metadata(tcx);
        flux_metadata::encode_metadata(genv, path.as_path());
    }
}

struct CrateChecker<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    cache: FixQueryCache,
}

impl<'genv, 'tcx> CrateChecker<'genv, 'tcx> {
    fn new(genv: GlobalEnv<'genv, 'tcx>) -> Self {
        CrateChecker { genv, cache: QueryCache::load() }
    }

    fn matches_check_def(&self, def_id: DefId) -> bool {
        let def_path = self.genv.tcx().def_path_str(def_id);
        def_path.contains(config::check_def())
    }

    /// Check whether the file where `def_id` is defined is included in the list of glob patterns.
    /// This function will conservatively return `true` if anything unexpected happens.
    fn file_is_included(&self, def_id: LocalDefId) -> bool {
        let tcx = self.genv.tcx();
        let span = tcx.def_span(def_id);
        let sm = tcx.sess.source_map();
        let FileName::Real(file_name) = sm.span_to_filename(span) else { return true };
        let mut file_path = file_name.local_path_if_available();

        // If the path is absolute try to normalize it to be relative to the working_dir
        if file_path.is_absolute() {
            let working_dir = tcx.sess.opts.working_dir.local_path_if_available();
            let Ok(p) = file_path.strip_prefix(working_dir) else { return true };
            file_path = p;
        }

        config::is_checked_file(file_path)
    }

    fn check_def_catching_bugs(&mut self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        let mut this = std::panic::AssertUnwindSafe(self);
        let msg = format!("def_id: {:?}, span: {:?}", def_id, this.genv.tcx().def_span(def_id));
        flux_common::bug::catch_bugs(&msg, move || this.check_def(def_id))?
    }

    fn check_def(&mut self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        let def_id = self.genv.maybe_extern_id(def_id);

        if !self.matches_check_def(def_id.resolved_id()) {
            return Ok(());
        }
        if self.genv.ignored(def_id.local_id()) || self.genv.is_dummy(def_id.local_id()) {
            return Ok(());
        }
        if !self.file_is_included(def_id.local_id()) {
            return Ok(());
        }

        match self.genv.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                // Make sure we run conversion and report errors even if we skip the function
                force_conv(self.genv, def_id.resolved_id()).emit(&self.genv)?;
                let Some(local_id) = def_id.as_local() else { return Ok(()) };
                refineck::check_fn(self.genv, &mut self.cache, local_id)
            }
            DefKind::Enum => {
                self.genv.check_wf(def_id.local_id()).emit(&self.genv)?;
                self.genv.variants_of(def_id).emit(&self.genv)?;
                let adt_def = self.genv.adt_def(def_id).emit(&self.genv)?;
                let enum_def = self
                    .genv
                    .map()
                    .expect_item(def_id.local_id())
                    .emit(&self.genv)?
                    .expect_enum();
                refineck::invariants::check_invariants(
                    self.genv,
                    &mut self.cache,
                    def_id,
                    enum_def.invariants,
                    &adt_def,
                )
            }
            DefKind::Struct => {
                // We check invariants for `struct` in `check_constructor` (i.e. when the struct is built).
                // However, we leave the below code in to force the queries that do the conversions that check
                // for ill-formed annotations e.g. see tests/tests/neg/error_messages/annot_check/struct_error.rs
                self.genv.check_wf(def_id.local_id()).emit(&self.genv)?;
                self.genv.adt_def(def_id).emit(&self.genv)?;
                self.genv.variants_of(def_id).emit(&self.genv)?;
                let _struct_def = self
                    .genv
                    .map()
                    .expect_item(def_id.local_id())
                    .emit(&self.genv)?
                    .expect_struct();
                Ok(())
            }
            DefKind::Impl { of_trait } => {
                self.genv.check_wf(def_id.local_id()).emit(&self.genv)?;
                if of_trait {
                    refineck::compare_impl_item::check_impl_against_trait(self.genv, def_id)
                        .emit(&self.genv)?;
                }
                Ok(())
            }
            DefKind::TyAlias => {
                self.genv.check_wf(def_id.local_id()).emit(&self.genv)?;
                self.genv.type_of(def_id).emit(&self.genv)?;
                Ok(())
            }
            DefKind::Trait => {
                self.genv.check_wf(def_id.local_id()).emit(&self.genv)?;
                Ok(())
            }
            _ => Ok(()),
        }
    }
}

fn force_conv(genv: GlobalEnv, def_id: DefId) -> QueryResult {
    genv.generics_of(def_id)?;
    genv.refinement_generics_of(def_id)?;
    genv.predicates_of(def_id)?;
    genv.fn_sig(def_id)?;
    Ok(())
}

fn mir_borrowck<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> query::queries::mir_borrowck::ProvidedValue<'tcx> {
    let bodies_with_facts = rustc_borrowck::consumers::get_bodies_with_borrowck_facts(
        tcx,
        def_id,
        ConsumerOptions::RegionInferenceContext,
    );
    for (def_id, body_with_facts) in bodies_with_facts {
        if config::dump_mir() {
            rustc_middle::mir::pretty::write_mir_fn(
                tcx,
                &body_with_facts.body,
                &mut |_, _| Ok(()),
                &mut dbg::writer_for_item(tcx, def_id.to_def_id(), "mir").unwrap(),
                rustc_middle::mir::pretty::PrettyPrintMirOptions::from_cli(tcx),
            )
            .unwrap();
        }

        // SAFETY: This is safe because we are feeding in the same `tcx` that is
        // going to be used as a witness when pulling out the data.
        unsafe {
            flux_common::mir_storage::store_mir_body(tcx, def_id, body_with_facts);
        }
    }
    let mut providers = query::Providers::default();
    rustc_borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}
