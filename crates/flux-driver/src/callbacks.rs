use std::{io, path::Path};

use flux_common::{bug, cache::QueryCache, iter::IterExt, result::ResultExt};
use flux_config::{self as config};
use flux_errors::FluxSession;
use flux_infer::{
    fixpoint_encoding::{ExprEncodingCtxt, FixQueryCache, SortEncodingCtxt},
    lean_encoding::LeanEncoder,
};
use flux_metadata::CStore;
use flux_middle::{
    Specs,
    def_id::MaybeExternId,
    fhir::{self, FluxItem},
    global_env::GlobalEnv,
    metrics::{self, Metric, TimingKind},
    queries::{Providers, QueryResult},
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
            let result = metrics::time_it(TimingKind::Total, || check_crate(genv));
            if result.is_ok() {
                encode_and_save_metadata(genv);
            }
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
        if config::emit_lean_defs() {
            ck.encode_flux_items_in_lean().unwrap_or(());
        }

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
        Self { genv, cache: QueryCache::load() }
    }

    pub(crate) fn encode_flux_items_in_lean(&self) -> Result<(), io::Error> {
        let mut ecx = ExprEncodingCtxt::new(self.genv, None);
        let mut scx = SortEncodingCtxt::default();
        let mut fun_defs = vec![];
        let mut opaque_fun_defs = vec![];
        for (def_id, flux_item) in self.genv.fhir_iter_flux_items() {
            ecx.declare_fun(def_id.to_def_id());
            match flux_item {
                FluxItem::Func(spec_func) if spec_func.body.is_some() => {
                    fun_defs.push(
                        ecx.fun_def_to_fixpoint(spec_func.def_id.to_def_id(), &mut scx)
                            .unwrap(),
                    );
                }
                FluxItem::Func(spec_func) => {
                    opaque_fun_defs
                        .push(ecx.fun_decl_to_fixpoint(spec_func.def_id.to_def_id(), &mut scx));
                }
                FluxItem::SortDecl(sort_decl) => {
                    scx.declare_opaque_sort(sort_decl.def_id.to_def_id());
                }
                _ => {}
            }
        }
        let opaque_sorts = scx.user_sorts_to_fixpoint(self.genv);
        let adt_defs = scx.encode_data_decls(self.genv).unwrap();
        if !opaque_sorts.is_empty()
            || !opaque_fun_defs.is_empty()
            || !adt_defs.is_empty()
            || !fun_defs.is_empty()
        {
            let encoder = LeanEncoder::new(
                self.genv,
                std::path::Path::new("./"),
                "lean_proofs".to_string(),
                "Defs".to_string(),
            );
            encoder
                .encode_defs(&opaque_sorts, &opaque_fun_defs, &adt_defs, &fun_defs)
                .unwrap();
        }
        Ok(())
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
    fn is_included(&self, def_id: MaybeExternId) -> bool {
        let Some(pattern) = config::include_pattern() else { return true };
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

    fn check_def_catching_bugs(&mut self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        let mut this = std::panic::AssertUnwindSafe(self);
        let msg = format!("def_id: {:?}, span: {:?}", def_id, this.genv.tcx().def_span(def_id));
        flux_common::bug::catch_bugs(&msg, move || this.check_def(def_id))?
    }

    fn check_def(&mut self, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
        let def_id = self.genv.maybe_extern_id(def_id);

        // Dummy items generated for extern specs are excluded from metrics
        if self.genv.is_dummy(def_id.local_id()) {
            return Ok(());
        }

        let kind = self.genv.def_kind(def_id);

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
                    && self.genv.tcx().is_mir_available(local_id)
            })
            .unwrap_or(false);

        metrics::incr_metric_if(is_fn_with_body, Metric::FnTotal);

        if self.genv.ignored(def_id.local_id()) {
            metrics::incr_metric_if(is_fn_with_body, Metric::FnIgnored);
            return Ok(());
        }
        if !self.is_included(def_id) {
            metrics::incr_metric_if(is_fn_with_body, Metric::FnTrusted);
            return Ok(());
        }

        match kind {
            DefKind::Fn | DefKind::AssocFn => {
                // Make sure we run conversion and report errors even if we skip the function
                force_conv(self.genv, def_id.resolved_id()).emit(&self.genv)?;
                let Some(local_id) = def_id.as_local() else { return Ok(()) };
                if is_fn_with_body {
                    refineck::check_fn(self.genv, &mut self.cache, local_id)?;
                }
                Ok(())
            }
            DefKind::Enum => {
                self.genv.check_wf(def_id.local_id()).emit(&self.genv)?;
                self.genv.variants_of(def_id).emit(&self.genv)?;
                let adt_def = self.genv.adt_def(def_id).emit(&self.genv)?;
                let enum_def = self
                    .genv
                    .fhir_expect_item(def_id.local_id())
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
                    .fhir_expect_item(def_id.local_id())
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
