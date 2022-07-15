#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/surface/rvec.rs"]
pub mod rvec;

use rvec::RVec;

#[flux::refined_by(n: int)]
pub struct Foo {
    #[flux::field(RVec<usize>[@n])]
    pub inner: RVec<usize>,
}

impl Foo {
    #[flux::sig(fn() -> Foo[0])]
    pub fn new() -> Foo {
        Self { inner: RVec::new() }
    }
}
