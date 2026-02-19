use std::path::Path;

use flux_common::{bug, cache::QueryCache, iter::IterExt, result::ResultExt};
use flux_config::{self as config, IncludePattern};
use flux_errors::FluxSession;
use flux_infer::{fixpoint_encoding::FixQueryCache, lean_encoding};
use flux_metadata::CStore;
use flux_middle::{
    Specs,
    def_id::MaybeExternId,
    fhir::{self},
    global_env::GlobalEnv,
    metrics::{self, Metric, TimingKind},
    queries::{Providers, QueryResult},
    rty::StaticInfo,
};
use flux_refineck as refineck;
use rustc_borrowck::consumers::ConsumerOptions;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    def::{CtorKind, DefKind},
    def_id::{LOCAL_CRATE, LocalDefId},
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
            let result = metrics::time_it(TimingKind::Total, || check_crate(genv));
            if result.is_ok() {
                encode_and_save_metadata(genv);
            }
            lean_encoding::finalize(genv).unwrap_or(());
        });
        let _ = metrics::print_and_dump_timings(tcx);
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

        // Iterate over all def ids including dummy items for extern specs
        let result = genv
            .tcx()
            .iter_local_def_id()
            .try_for_each_exhaust(|def_id| ck.check_def_catching_bugs(def_id));

        if config::lean().is_emit() {
            lean_encoding::finalize(genv)
                .unwrap_or_else(|err| bug!("error running lean-check {err:?}"));
        }

        let lean_result = if config::lean().is_check() {
            genv.iter_local_def_id().try_for_each_exhaust(|def_id| {
                if genv.proven_externally(def_id).is_some() {
                    lean_encoding::check_proof(genv, def_id.to_def_id())
                } else {
                    Ok(())
                }
            })
        } else {
            Ok(())
        };

        ck.cache.save().unwrap_or(());

        tracing::info!("Callbacks::check_crate");

        result.and(lean_result)
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
        Self { genv, cache: QueryCache::load() }
    }

    fn matches_def(&self, def_id: MaybeExternId, def: &str) -> bool {
        // Does this def_id's name contain `fn_name`?
        let def_path = self.genv.tcx().def_path_str(def_id.local_id());
        def_path.contains(def)
    }

    fn matches_file_path<F>(&self, def_id: MaybeExternId, matcher: F) -> bool
    where
        F: Fn(&Path) -> bool,
    {
        let def_id = def_id.local_id();
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

        matcher(file_path)
    }

    fn matches_pos(&self, def_id: MaybeExternId, line: usize, col: usize) -> bool {
        let def_id = def_id.local_id();
        let tcx = self.genv.tcx();
        let hir_id = tcx.local_def_id_to_hir_id(def_id);
        let body_span = tcx.hir_span_with_body(hir_id);
        let source_map = tcx.sess.source_map();
        let lo_pos = source_map.lookup_char_pos(body_span.lo());
        let start_line = lo_pos.line;
        let start_col = lo_pos.col_display;
        let hi_pos = source_map.lookup_char_pos(body_span.hi());
        let end_line = hi_pos.line;
        let end_col = hi_pos.col_display;

        // is the line in the range of the body?
        if start_line < end_line {
            // multiple lines: check if the line is in the range
            start_line <= line && line <= end_line
        } else {
            // single line: check if the line is the same and the column is in range
            start_line == line && start_col <= col && col <= end_col
        }
    }

    /// Check whether the `def_id` (or the file where `def_id` is defined)
    /// is in the `include` pattern, and conservatively return `true` if
    /// anything unexpected happens.
    fn matches_pattern(&self, def_id: MaybeExternId, pattern: &IncludePattern) -> bool {
        if self.matches_file_path(def_id, |path| pattern.glob.is_match(path)) {
            return true;
        }
        if pattern.defs.iter().any(|def| self.matches_def(def_id, def)) {
            return true;
        }
        if pattern.spans.iter().any(|pos| {
            self.matches_file_path(def_id, |path| path.ends_with(&pos.file))
                && self.matches_pos(def_id, pos.line, pos.column)
        }) {
            return true;
        }
        false
    }

    /// Check whether the `def_id` (or the file where `def_id` is defined)
    /// is in the `trusted` pattern, and conservatively return `false` if
    /// anything unexpected happens.
    fn is_trusted(&self, def_id: MaybeExternId) -> bool {
        let Some(pattern) = config::trusted_pattern() else { return false };
        self.matches_pattern(def_id, pattern)
    }

    /// Check whether the `def_id` (or the file where `def_id` is defined)
    /// is in the `include` pattern, and conservatively return `true` if
    /// anything unexpected happens.
    fn matches_included_pattern(&self, def_id: MaybeExternId) -> bool {
        let Some(pattern) = config::include_pattern() else { return true };
        self.matches_pattern(def_id, pattern)
    }

    fn is_included(&self, def_id: MaybeExternId) -> bool {
        self.matches_included_pattern(def_id) || self.is_trusted(def_id)
    }

    fn check_def_catching_bugs(&mut self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        let mut this = std::panic::AssertUnwindSafe(self);
        let msg = format!("def_id: {:?}, span: {:?}", def_id, this.genv.tcx().def_span(def_id));
        flux_common::bug::catch_bugs(&msg, move || this.check_def(def_id))?
    }

    fn check_def(&mut self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        let genv = self.genv;
        let def_id = genv.maybe_extern_id(def_id);

        // Dummy items generated for extern specs are excluded from metrics
        if genv.is_dummy(def_id.local_id()) {
            return Ok(());
        }

        let kind = genv.def_kind(def_id);

        // For the purpose of metrics, we consider to be a *function* an item that
        // 1. It's local, i.e., it's not an extern spec.
        // 2. It's a free function (`DefKind::Fn`) or associated item (`DefKind::AssocFn`), and
        // 3. It has a mir body
        // In particular, this excludes closures (because they dont have the right `DefKind`) and
        // trait methods without a default body.
        let is_fn_with_body = def_id
            .as_local()
            .map(|local_id| {
                matches!(kind, DefKind::Fn | DefKind::AssocFn)
                    && genv.tcx().is_mir_available(local_id)
            })
            .unwrap_or(false);

        metrics::incr_metric_if(is_fn_with_body, Metric::FnTotal);

        if genv.ignored(def_id.local_id()) {
            metrics::incr_metric_if(is_fn_with_body, Metric::FnIgnored);
            return Ok(());
        }
        if !self.is_included(def_id) {
            metrics::incr_metric_if(is_fn_with_body, Metric::FnTrusted);
            return Ok(());
        }

        trigger_queries(genv, def_id).emit(&genv)?;

        match kind {
            DefKind::Fn | DefKind::AssocFn => {
                let Some(local_id) = def_id.as_local() else { return Ok(()) };
                if is_fn_with_body {
                    refineck::check_fn(genv, &mut self.cache, local_id)?;
                }
            }
            DefKind::Enum => {
                let adt_def = genv.adt_def(def_id).emit(&genv)?;
                let enum_def = genv
                    .fhir_expect_item(def_id.local_id())
                    .emit(&genv)?
                    .expect_enum();
                refineck::invariants::check_invariants(
                    genv,
                    &mut self.cache,
                    def_id,
                    enum_def.invariants,
                    &adt_def,
                )?;
            }
            DefKind::Struct => {
                // We check invariants for `struct` in `check_constructor` (i.e. when the struct is built),
                // so nothing to do here.
            }
            DefKind::Impl { of_trait } => {
                if of_trait {
                    refineck::compare_impl_item::check_impl_against_trait(genv, def_id)
                        .emit(&genv)?;
                }
            }
            DefKind::TyAlias => {}
            DefKind::Trait => {}
            DefKind::Static { .. } => {
                if let StaticInfo::Known(ty) = genv.static_info(def_id).emit(&genv)?
                    && let Some(local_id) = def_id.as_local()
                {
                    refineck::check_static(genv, &mut self.cache, local_id, ty)?;
                }
            }
            _ => (),
        }
        Ok(())
    }
}

/// Triggers queries for the given `def_id` to mark it as "reached" for metadata encoding.
///
/// This function ensures that all relevant queries for a definition are triggered upfront,
/// so the item and its associated data will be included in the encoded metadata. Without this,
/// items might be missing from the metadata (extern specs in particular which are not otherwise "checked"),
/// causing errors when dependent crates try to use them.
fn trigger_queries(genv: GlobalEnv, def_id: MaybeExternId) -> QueryResult {
    match genv.def_kind(def_id) {
        DefKind::Trait => {
            genv.generics_of(def_id)?;
            genv.predicates_of(def_id)?;
            genv.refinement_generics_of(def_id)?;
        }
        DefKind::Impl { .. } => {
            genv.generics_of(def_id)?;
            genv.predicates_of(def_id)?;
            genv.refinement_generics_of(def_id)?;
        }
        DefKind::Fn | DefKind::AssocFn => {
            genv.generics_of(def_id)?;
            genv.refinement_generics_of(def_id)?;
            genv.predicates_of(def_id)?;
            genv.fn_sig(def_id)?;
        }
        DefKind::Ctor(_, CtorKind::Fn) => {
            genv.generics_of(def_id)?;
            genv.refinement_generics_of(def_id)?;
            // We don't report the error because it can raise a `QueryErr::OpaqueStruct`,  which
            // should be reported at the use site.
            let _ = genv.fn_sig(def_id);
        }
        DefKind::Enum | DefKind::Struct => {
            genv.generics_of(def_id)?;
            genv.predicates_of(def_id)?;
            genv.refinement_generics_of(def_id)?;
            genv.adt_def(def_id)?;
            genv.adt_sort_def_of(def_id)?;
            genv.variants_of(def_id)?;
            genv.type_of(def_id)?;
        }
        DefKind::TyAlias => {
            genv.generics_of(def_id)?;
            genv.predicates_of(def_id)?;
            genv.refinement_generics_of(def_id)?;
            genv.type_of(def_id)?;
        }
        DefKind::OpaqueTy => {
            genv.generics_of(def_id)?;
            genv.predicates_of(def_id)?;
            genv.item_bounds(def_id)?;
            genv.refinement_generics_of(def_id)?;
        }
        _ => {}
    }
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
