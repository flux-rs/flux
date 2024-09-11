#![allow(incomplete_features)]
#![feature(rustc_private, specialization, if_let_guard)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_macros;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_type_ir;

mod decoder;
mod encoder;

use std::{hash::Hash, path::PathBuf};

use decoder::decode_crate_metadata;
use derive_where::derive_where;
use flux_errors::FluxSession;
use flux_macros::fluent_messages;
use flux_middle::{
    cstore::{CrateStore, OptResult},
    global_env::GlobalEnv,
    intern::List,
    queries::QueryResult,
    rty,
};
use rustc_data_structures::unord::{ExtendUnord, UnordMap};
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::ty::TyCtxt;
use rustc_session::{
    config::{OutFileName, OutputType},
    utils::CanonicalizedPath,
};
use rustc_span::{
    def_id::{CrateNum, DefId, DefIndex},
    Symbol,
};

pub use crate::encoder::encode_metadata;

fluent_messages! { "../locales/en-US.ftl" }

const METADATA_VERSION: u8 = 0;
const METADATA_HEADER: &[u8] = &[b'f', b'l', b'u', b'x', 0, 0, 0, METADATA_VERSION];

#[derive(Default)]
pub struct CStore {
    local_tables: UnordMap<CrateNum, Tables<DefIndex>>,
    extern_tables: Tables<DefId>,
}

#[derive(Default, TyEncodable, TyDecodable)]
pub struct CrateMetadata {
    local_tables: Tables<DefIndex>,
    extern_tables: Tables<DefId>,
}

/// Trait to deal with the fact that `assoc_refinmenents_of` and `assoc_refinements_def` use
/// `(K, Symbol)` as key;
trait Key {
    type KeyIndex;
    fn crate_num(self) -> CrateNum;
    fn to_index(self) -> Self::KeyIndex;
    fn name(self, tcx: TyCtxt) -> String;
}

impl Key for DefId {
    type KeyIndex = DefIndex;

    fn crate_num(self) -> CrateNum {
        self.krate
    }

    fn to_index(self) -> Self::KeyIndex {
        self.index
    }

    fn name(self, tcx: TyCtxt) -> String {
        tcx.def_path_str(self)
    }
}

impl Key for (DefId, Symbol) {
    type KeyIndex = (DefIndex, Symbol);

    fn crate_num(self) -> CrateNum {
        self.0.krate
    }

    fn to_index(self) -> Self::KeyIndex {
        (self.0.index, self.1)
    }

    fn name(self, tcx: TyCtxt) -> String {
        format!("{}::{}", tcx.def_path_str(self.0), self.1)
    }
}

#[derive_where(Default)]
#[derive(TyEncodable, TyDecodable)]
pub struct Tables<K: Eq + Hash> {
    generics_of: UnordMap<K, QueryResult<rty::Generics>>,
    refinement_generics_of: UnordMap<K, QueryResult<rty::RefinementGenerics>>,
    predicates_of: UnordMap<K, QueryResult<rty::EarlyBinder<rty::GenericPredicates>>>,
    item_bounds: UnordMap<K, QueryResult<rty::EarlyBinder<List<rty::Clause>>>>,
    assoc_refinements_of: UnordMap<K, QueryResult<rty::AssocRefinements>>,
    assoc_refinements_def: UnordMap<(K, Symbol), QueryResult<rty::EarlyBinder<rty::Lambda>>>,
    default_assoc_refinements_def:
        UnordMap<(K, Symbol), QueryResult<Option<rty::EarlyBinder<rty::Lambda>>>>,
    sort_of_assoc_reft: UnordMap<(K, Symbol), QueryResult<Option<rty::EarlyBinder<rty::FuncSort>>>>,
    fn_sig: UnordMap<K, QueryResult<rty::EarlyBinder<rty::PolyFnSig>>>,
    adt_def: UnordMap<K, QueryResult<rty::AdtDef>>,
    adt_sort_def: UnordMap<K, QueryResult<rty::AdtSortDef>>,
    variants: UnordMap<K, QueryResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>>>,
    type_of: UnordMap<K, QueryResult<rty::EarlyBinder<rty::TyCtor>>>,
}

impl CStore {
    pub fn load(tcx: TyCtxt, sess: &FluxSession) -> Self {
        let mut cstore = CStore::default();
        for crate_num in tcx.crates(()) {
            let Some(path) = flux_metadata_extern_location(tcx, *crate_num) else { continue };
            let Some(meta) = decode_crate_metadata(tcx, sess, path.as_path()) else { continue };
            cstore.local_tables.insert(*crate_num, meta.local_tables);
            cstore.merge_extern_tables(tcx, sess, meta.extern_tables);
        }
        cstore
    }

    fn merge_extern_tables(
        &mut self,
        tcx: TyCtxt,
        sess: &FluxSession,
        extern_tables: Tables<DefId>,
    ) {
        macro_rules! merge_extern_table {
            ($self:expr, $tcx:expr, $table:ident, $extern_tables:expr) => {{
                // This is technically observing the order becauses it has side effects, but it's ok
                // because we emit a fatal error and abort the process
                $extern_tables.$table.keys().map(|k| {
                    if self.$table(*k).is_some() {
                        sess.emit_fatal(errors::DuplicateSpec::new($tcx, *k));
                    }
                });
                $self
                    .extern_tables
                    .$table
                    .extend_unord(extern_tables.$table.into_items());
            }};
        }
        merge_extern_table!(self, tcx, generics_of, extern_tables);
        merge_extern_table!(self, tcx, refinement_generics_of, extern_tables);
        merge_extern_table!(self, tcx, predicates_of, extern_tables);
        merge_extern_table!(self, tcx, item_bounds, extern_tables);
        merge_extern_table!(self, tcx, assoc_refinements_of, extern_tables);
        merge_extern_table!(self, tcx, assoc_refinements_def, extern_tables);
        merge_extern_table!(self, tcx, sort_of_assoc_reft, extern_tables);
        merge_extern_table!(self, tcx, fn_sig, extern_tables);
        merge_extern_table!(self, tcx, adt_def, extern_tables);
        merge_extern_table!(self, tcx, adt_sort_def, extern_tables);
        merge_extern_table!(self, tcx, variants, extern_tables);
        merge_extern_table!(self, tcx, type_of, extern_tables);
    }
}

macro_rules! get {
    ($self:expr, $table:ident, $key:expr) => {{
        let key = $key;
        let this = $self;
        if let Some(tables) = this.local_tables.get(&key.crate_num()) {
            tables.$table.get(&key.to_index()).cloned()
        } else {
            this.extern_tables.$table.get(&key).cloned()
        }
    }};
}

impl CrateStore for CStore {
    fn fn_sig(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<rty::PolyFnSig>> {
        get!(self, fn_sig, def_id)
    }

    fn adt_def(&self, def_id: DefId) -> OptResult<rty::AdtDef> {
        get!(self, adt_def, def_id)
    }

    fn adt_sort_def(&self, def_id: DefId) -> OptResult<rty::AdtSortDef> {
        get!(self, adt_sort_def, def_id)
    }

    fn variants(
        &self,
        def_id: DefId,
    ) -> OptResult<rty::Opaqueness<rty::EarlyBinder<rty::PolyVariants>>> {
        get!(self, variants, def_id)
    }

    fn type_of(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<rty::TyCtor>> {
        get!(self, type_of, def_id)
    }

    fn generics_of(&self, def_id: DefId) -> OptResult<rty::Generics> {
        get!(self, generics_of, def_id)
    }

    fn refinement_generics_of(&self, def_id: DefId) -> OptResult<rty::RefinementGenerics> {
        get!(self, refinement_generics_of, def_id)
    }

    fn item_bounds(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<List<rty::Clause>>> {
        get!(self, item_bounds, def_id)
    }

    fn predicates_of(&self, def_id: DefId) -> OptResult<rty::EarlyBinder<rty::GenericPredicates>> {
        get!(self, predicates_of, def_id)
    }

    fn assoc_refinements_of(&self, def_id: DefId) -> OptResult<rty::AssocRefinements> {
        get!(self, assoc_refinements_of, def_id)
    }

    fn assoc_refinements_def(
        &self,
        key: (DefId, Symbol),
    ) -> OptResult<rty::EarlyBinder<rty::Lambda>> {
        get!(self, assoc_refinements_def, key)
    }

    fn default_assoc_refinements_def(
        &self,
        key: (DefId, Symbol),
    ) -> OptResult<Option<rty::EarlyBinder<rty::Lambda>>> {
        get!(self, default_assoc_refinements_def, key)
    }

    fn sort_of_assoc_reft(
        &self,
        key: (DefId, Symbol),
    ) -> OptResult<Option<rty::EarlyBinder<rty::FuncSort>>> {
        get!(self, sort_of_assoc_reft, key)
    }
}

impl CrateMetadata {
    fn new(genv: GlobalEnv) -> Self {
        let mut local_tables = Tables::default();
        encode_def_ids(
            genv,
            genv.iter_local_def_id().map(LocalDefId::to_def_id),
            &mut local_tables,
            |def_id| def_id.index,
        );

        let mut extern_tables = Tables::default();
        encode_def_ids(genv, genv.iter_extern_def_id(), &mut extern_tables, |def_id| def_id);

        CrateMetadata { local_tables, extern_tables }
    }
}

fn encode_def_ids<K: Eq + Hash + Copy>(
    genv: GlobalEnv,
    def_ids: impl IntoIterator<Item = DefId>,
    tables: &mut Tables<K>,
    mk_key: impl Fn(DefId) -> K,
) {
    for def_id in def_ids {
        let def_kind = genv.def_kind(def_id);
        let key = mk_key(def_id);

        match def_kind {
            DefKind::Trait => {
                tables.generics_of.insert(key, genv.generics_of(def_id));
                tables.predicates_of.insert(key, genv.predicates_of(def_id));
                tables
                    .refinement_generics_of
                    .insert(key, genv.refinement_generics_of(def_id));
                let assocs = genv.assoc_refinements_of(def_id);
                if let Ok(assocs) = &assocs {
                    for assoc in &assocs.items {
                        let key = mk_key(assoc.container_def_id);
                        tables.default_assoc_refinements_def.insert(
                            (key, assoc.name),
                            genv.default_assoc_refinement_def(assoc.container_def_id, assoc.name),
                        );
                        tables.sort_of_assoc_reft.insert(
                            (key, assoc.name),
                            genv.sort_of_assoc_reft(assoc.container_def_id, assoc.name),
                        );
                    }
                }
                tables.assoc_refinements_of.insert(key, assocs);
            }
            DefKind::Impl { of_trait } => {
                tables.generics_of.insert(key, genv.generics_of(def_id));
                tables.predicates_of.insert(key, genv.predicates_of(def_id));
                tables
                    .refinement_generics_of
                    .insert(key, genv.refinement_generics_of(def_id));

                if of_trait {
                    let assocs = genv.assoc_refinements_of(def_id);
                    if let Ok(assocs) = &assocs {
                        for assoc in &assocs.items {
                            let key = mk_key(assoc.container_def_id);
                            tables.assoc_refinements_def.insert(
                                (key, assoc.name),
                                genv.assoc_refinement_def(assoc.container_def_id, assoc.name),
                            );
                            tables.sort_of_assoc_reft.insert(
                                (key, assoc.name),
                                genv.sort_of_assoc_reft(assoc.container_def_id, assoc.name),
                            );
                        }
                    }
                    tables.assoc_refinements_of.insert(key, assocs);
                }
            }
            DefKind::Fn | DefKind::AssocFn => {
                tables.generics_of.insert(key, genv.generics_of(def_id));
                tables.predicates_of.insert(key, genv.predicates_of(def_id));
                tables
                    .refinement_generics_of
                    .insert(key, genv.refinement_generics_of(def_id));
                tables.fn_sig.insert(key, genv.fn_sig(def_id));
            }
            DefKind::Enum | DefKind::Struct => {
                tables.generics_of.insert(key, genv.generics_of(def_id));
                tables.predicates_of.insert(key, genv.predicates_of(def_id));
                tables
                    .refinement_generics_of
                    .insert(key, genv.refinement_generics_of(def_id));
                tables.adt_def.insert(key, genv.adt_def(def_id));
                tables
                    .adt_sort_def
                    .insert(key, genv.adt_sort_def_of(def_id));
                tables.variants.insert(key, genv.variants_of(def_id));
                tables.type_of.insert(key, genv.type_of(def_id));
            }
            DefKind::TyAlias { .. } => {
                tables.generics_of.insert(key, genv.generics_of(def_id));
                tables.predicates_of.insert(key, genv.predicates_of(def_id));
                tables
                    .refinement_generics_of
                    .insert(key, genv.refinement_generics_of(def_id));
                tables
                    .adt_sort_def
                    .insert(key, genv.adt_sort_def_of(def_id));
                tables.type_of.insert(key, genv.type_of(def_id));
            }
            DefKind::OpaqueTy => {
                tables.generics_of.insert(key, genv.generics_of(def_id));
                tables.predicates_of.insert(key, genv.predicates_of(def_id));
                tables.item_bounds.insert(key, genv.item_bounds(def_id));
                tables
                    .refinement_generics_of
                    .insert(key, genv.refinement_generics_of(def_id));
            }
            _ => {}
        }
    }
}

pub fn filename_for_metadata(tcx: TyCtxt) -> OutFileName {
    match rustc_session::output::filename_for_metadata(tcx.sess, tcx.output_filenames(())) {
        OutFileName::Real(path) => OutFileName::Real(path.with_extension("fluxmeta")),
        OutFileName::Stdout => OutFileName::Stdout,
    }
}

fn flux_metadata_extern_location(tcx: TyCtxt, crate_num: CrateNum) -> Option<PathBuf> {
    let crate_name = tcx.crate_name(crate_num);
    let path = tcx
        .sess
        .opts
        .externs
        .get(crate_name.as_str())?
        .files()
        .into_iter()
        .flatten()
        .map(CanonicalizedPath::canonicalized)
        .find(|path| path.extension().unwrap_or_default() == OutputType::Metadata.extension())?;
    Some(path.with_extension("fluxmeta"))
}

// Tags for encoding Symbol's
const SYMBOL_STR: u8 = 0;
const SYMBOL_OFFSET: u8 = 1;
const SYMBOL_PREINTERNED: u8 = 2;

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use rustc_middle::ty::TyCtxt;

    use crate::Key;

    #[derive(Diagnostic)]
    #[diag(metadata_duplicate_spec, code = E0999)]
    pub(super) struct DuplicateSpec {
        def_name: String,
    }

    impl DuplicateSpec {
        pub(super) fn new(tcx: TyCtxt, key: impl Key) -> Self {
            Self { def_name: key.name(tcx) }
        }
    }
}
