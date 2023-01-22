#![allow(incomplete_features)]
#![feature(rustc_private, specialization)]

extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_type_ir;

mod decoder;
mod encoder;

use flux_middle::rty;
use rustc_hash::FxHashMap;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_span::def_id::DefIndex;

#[derive(TyEncodable, TyDecodable)]
pub struct CrateRoot {
    type_of: FxHashMap<DefIndex, rty::Ty>,
}
