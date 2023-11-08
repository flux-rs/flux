#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::refined_by(n: int)]
pub struct S {
    #[flux::field(usize[n])]
    pub size: usize,
    #[flux::field(RVec<i32>[n])]
    pub payload: RVec<i32>,
}

impl S {
    #[flux::sig(fn(z: &strg RVec<i32>) ensures z: RVec<i32>)]
    fn bar(z: &mut RVec<i32>) {
        z.push(10)
    }

    #[flux::sig(fn(self: &S) -> i32)]
    fn moo(&self) -> i32 {
        0
    }

    #[flux::sig(fn(self: &mut S) -> i32)]
    fn choo(&mut self) -> i32 {
        0
    }

    // no sig = 'internal compiler error'
    #[flux::sig(fn(z: &strg S[@n]) ensures z: S)]
    pub fn test0(z: &mut S) {
        Self::bar(&mut z.payload);
        z.moo(); //~ ERROR type invariant may not hold
    }

    #[flux::sig(fn(z: &strg S[@n]) ensures z: S)]
    pub fn test1(z: &mut S) {
        Self::bar(&mut z.payload);
        z.choo(); //~ ERROR type invariant may not hold
    }
}
