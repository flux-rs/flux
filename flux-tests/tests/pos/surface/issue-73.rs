#![allow(unused_attributes)]
#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rmat.rs"]
pub mod rmat;
use rmat::RMat;

#[flux::sig(fn(&RMat<f32>) -> bool)]
pub fn is_neg(_arr2: &RMat<f32>) -> bool {
    true
}

#[flux::sig(fn(&mut RMat<f32>) -> bool)]
pub fn is_neg_mut(_arr2: &mut RMat<f32>) -> bool {
    true
}
