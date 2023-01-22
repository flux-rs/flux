#![allow(incomplete_features)]
#![feature(rustc_private, specialization)]

extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_macros;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_type_ir;

mod decoder;
mod encoder;

use flux_middle::{global_env::GlobalEnv, rty};
use rustc_hash::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_span::def_id::DefIndex;

pub use crate::encoder::encode_metadata;

const METADATA_VERSION: u8 = 0;
const METADATA_HEADER: &[u8] = &[b'f', b'l', b'u', b'x', 0, 0, 0, METADATA_VERSION];

#[derive(TyEncodable, TyDecodable)]
pub struct CrateRoot {
    fn_sigs: FxHashMap<DefIndex, rty::PolySig>,
}

impl CrateRoot {
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
