#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/surface/rvec.rs"]
pub mod rvec;

use rvec::RVec;

#[lr::refined_by(n: int)]
pub struct Foo {
    #[lr::field(RVec<usize>[@n])]
    inner: RVec<usize>,
}

impl Foo {
    #[lr::sig(fn() -> Foo[0])]
    pub fn new() -> Foo {
        Self { inner: RVec::new() }
    }
}
