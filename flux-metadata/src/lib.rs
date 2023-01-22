#![allow(incomplete_features)]
#![feature(rustc_private, specialization)]

extern crate rustc_data_structures;
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
use flux_middle::{cstore::CrateStore, global_env::GlobalEnv, rty};
use rustc_hash::FxHashMap;
use rustc_hir::{def::DefKind, def_id::LOCAL_CRATE};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::ty::TyCtxt;
use rustc_session::{config::OutputType, utils::CanonicalizedPath};
use rustc_span::def_id::{CrateNum, DefId, DefIndex};

pub use crate::encoder::encode_metadata;

const METADATA_VERSION: u8 = 0;
const METADATA_HEADER: &[u8] = &[b'f', b'l', b'u', b'x', 0, 0, 0, METADATA_VERSION];

pub struct CStore {
    meta: FxHashMap<CrateNum, CrateMetadata>,
}

#[derive(TyEncodable, TyDecodable)]
pub struct CrateMetadata {
    fn_sigs: FxHashMap<DefIndex, rty::PolySig>,
}

impl CStore {
    pub fn load(tcx: TyCtxt, sess: &FluxSession) -> Self {
        let meta = tcx
            .crates(())
            .iter()
            .filter_map(|crate_num| {
                let path = flux_metadata_extern_location(tcx, *crate_num)?;
                let meta = decode_crate_metadata(tcx, sess, path.as_path());
                Some((*crate_num, meta))
            })
            .collect();
        Self { meta }
    }
}

impl CrateStore for CStore {
    fn fn_sig(&self, def_id: DefId) -> Option<rty::PolySig> {
        self.meta
            .get(&def_id.krate)?
            .fn_sigs
            .get(&def_id.index)
            .cloned()
    }
}

impl CrateMetadata {
    fn new(genv: &GlobalEnv) -> Self {
        let tcx = genv.tcx;
        let mut fn_sigs = FxHashMap::default();

        for local_id in tcx.iter_local_def_id() {
            let def_id = local_id.to_def_id();
            let def_kind = tcx.def_kind(local_id);

            match def_kind {
                DefKind::Fn | DefKind::AssocFn => {
                    fn_sigs.insert(
                        def_id.index,
                        genv.lookup_fn_sig(def_id)
                            .unwrap_or_else(|err| genv.sess.emit_fatal(err)),
                    );
                }
                DefKind::Enum | DefKind::Struct => {
                    // println!("adt {:?}", tcx.def_path_str(def_id));
                }
                DefKind::Variant => {
                    // println!("variant {:?}", tcx.def_path_str(def_id));
                }
                _ => {}
            }
        }
        Self { fn_sigs }
    }
}

pub fn filename_for_metadata(tcx: TyCtxt) -> PathBuf {
    let crate_name = tcx.crate_name(LOCAL_CRATE);
    rustc_session::output::filename_for_metadata(tcx.sess, crate_name, tcx.output_filenames(()))
        .with_extension("fluxmeta")
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
