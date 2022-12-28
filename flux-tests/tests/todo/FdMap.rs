#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::refined_by(n: int)]
pub struct FdMap {
    #[flux::field(RVec<usize>[@n])]
    pub reserve: RVec<usize>,
}

impl FdMap {
    #[flux::sig(fn (self: &strg FdMap[@n], k: usize) ensures self: FdMap[n+1])]
    pub fn delete(&mut self, k: usize) {
        self.reserve.push(k);
    }
}

pub struct Thing {
    pub fdmap: FdMap,
}

#[flux::sig(fn (t: &strg Thing) ensures t: Thing)]
pub fn test(t: &mut Thing) {
    t.fdmap.delete(10);
}
