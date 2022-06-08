#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/surface/rvec.rs"]
pub mod rvec;

use rvec::RVec;

#[flux::refined_by(n: int)]
pub struct Foo {
    #[flux::field(RVec<usize>[@n])]
    inner: RVec<usize>,
}

impl Foo {
    #[flux::sig(fn() -> Foo[10])]
    pub fn new() -> Foo { //~ ERROR postcondition might not hold
        Self { inner: RVec::new() }
    }
}
