#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/surface/rvec.rs"]
pub mod rvec;

use rvec::RVec;

#[lr::refined_by(x: int)]
pub struct Foo {
    #[lr::field(RVec<usize>@x)]
    inner: RVec<usize>,
}

impl Foo {
    #[lr::sig(fn() -> Foo[10])] //~ ERROR postcondition might not hold
    pub fn new() -> Foo {
        Self { inner: RVec::new() }
    }
}