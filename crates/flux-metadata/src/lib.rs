#![allow(incomplete_features)]
#![feature(rustc_private, specialization, if_let_guard)]

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

use std::path::PathBuf;

use decoder::decode_crate_metadata;
use flux_errors::FluxSession;
use flux_macros::fluent_messages;
use flux_middle::{cstore::CrateStore, global_env::GlobalEnv, intern::List, rty};
use rustc_errors::{DiagnosticMessage, SubdiagnosticMessage};
use rustc_hash::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::ty::TyCtxt;
use rustc_session::{
    config::{OutFileName, OutputType},
    utils::CanonicalizedPath,
};
use rustc_span::def_id::{CrateNum, DefId, DefIndex};

pub use crate::encoder::encode_metadata;

fluent_messages! { "../locales/en-US.ftl" }

const METADATA_VERSION: u8 = 0;
const METADATA_HEADER: &[u8] = &[b'f', b'l', b'u', b'x', 0, 0, 0, METADATA_VERSION];

pub struct CStore {
    meta: FxHashMap<CrateNum, CrateMetadata>,
}

#[derive(TyEncodable, TyDecodable)]
pub struct CrateMetadata {
    fn_sigs: FxHashMap<DefIndex, rty::EarlyBinder<rty::PolyFnSig>>,
    adts: FxHashMap<DefIndex, AdtMetadata>,
    /// For now it only store type of aliases
    type_of: FxHashMap<DefIndex, rty::EarlyBinder<rty::TyCtor>>,
}

#[derive(TyEncodable, TyDecodable)]
struct AdtMetadata {
    adt_def: rty::AdtDef,
    variants: rty::Opaqueness<rty::EarlyBinder<List<rty::PolyVariant>>>,
}

impl CStore {
    pub fn load(tcx: TyCtxt, sess: &FluxSession) -> Self {
        let meta = tcx
            .crates(())
            .iter()
            .filter_map(|crate_num| {
                let path = flux_metadata_extern_location(tcx, *crate_num)?;
                let meta = decode_crate_metadata(tcx, sess, path.as_path())?;
                Some((*crate_num, meta))
            })
            .collect();
        Self { meta }
    }

    fn adt(&self, def_id: DefId) -> Option<&AdtMetadata> {
        self.meta.get(&def_id.krate)?.adts.get(&def_id.index)
    }
}

impl CrateStore for CStore {
    fn fn_sig(&self, def_id: DefId) -> Option<rty::EarlyBinder<rty::PolyFnSig>> {
        self.meta
            .get(&def_id.krate)?
            .fn_sigs
            .get(&def_id.index)
            .cloned()
    }

    fn adt_def(&self, def_id: DefId) -> Option<&rty::AdtDef> {
        self.adt(def_id).map(|adt| &adt.adt_def)
    }

    fn variants(
        &self,
        def_id: DefId,
    ) -> Option<rty::Opaqueness<rty::EarlyBinder<&[rty::PolyVariant]>>> {
        self.adt(def_id)
            .map(|adt| adt.variants.as_ref().map(rty::EarlyBinder::as_deref))
    }

    fn type_of(&self, def_id: DefId) -> Option<&rty::EarlyBinder<rty::TyCtor>> {
        self.meta.get(&def_id.krate)?.type_of.get(&def_id.index)
    }
}

impl CrateMetadata {
    fn new(genv: &GlobalEnv) -> Self {
        let tcx = genv.tcx();
        let mut fn_sigs = FxHashMap::default();
        let mut adts = FxHashMap::default();
        let mut type_of = FxHashMap::default();

        for local_id in tcx.iter_local_def_id() {
            let def_id = local_id.to_def_id();
            let def_kind = tcx.def_kind(local_id);

            match def_kind {
                DefKind::Fn | DefKind::AssocFn => {
                    fn_sigs.insert(def_id.index, genv.fn_sig(def_id).unwrap());
                }
                DefKind::Enum | DefKind::Struct => {
                    let adt_def = genv.adt_def(def_id).unwrap();
                    let variants = genv.variants_of(def_id).unwrap();
                    let meta = AdtMetadata { adt_def, variants };
                    adts.insert(def_id.index, meta);
                    type_of.insert(def_id.index, genv.type_of(def_id).unwrap());
                }
                DefKind::TyAlias { .. } => {
                    type_of.insert(def_id.index, genv.type_of(def_id).unwrap());
                }
                _ => {}
            }
        }
        Self { fn_sigs, adts, type_of }
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
