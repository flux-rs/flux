#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::refined_by(reserve_len: int, counter: int)]
pub struct FdMap {
    #[flux::field(RVec<usize>[@reserve_len])]
    pub reserve: RVec<usize>,
}

#[flux::sig(fn (&mut FdMap[@dummy], k: usize) )]
pub fn delete(fdmap: &mut FdMap, k: usize) {
    fdmap.reserve.push(k); // FLUX-TODO: this line triggers a crash at flux-typeck/src/constraint_gen.rs:360:18
}
