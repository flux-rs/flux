#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
pub mod rvec;

use rvec::RVec;

#[flux::refined_by(len: int)]
pub struct Vecs {
    #[flux::field(RVec<i32>[@len])]
    pub my: RVec<i32>,
}

#[flux::sig(fn(vecs: &strg Vecs[@n], i32) ensures vecs: Vecs[n])]
pub fn push(vecs: &mut Vecs, value: i32) {
    //~^ ERROR refinement type
    vecs.my.push(value);
}
