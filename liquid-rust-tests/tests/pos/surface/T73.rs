#![allow(unused_attributes)]
#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/rmat.rs"]
pub mod rmat;
use rmat::RMat;

#[lr::sig(fn(&RMat<f32>) -> bool)]
pub fn is_neg(_arr2: &RMat<f32>) -> bool {
    true
}
