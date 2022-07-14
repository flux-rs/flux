#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

#[flux::sig(fn(RVec<i32{v:0<=v}>) -> ())]
pub fn test_loop(vec: RVec<i32>) {
    for val in vec {
        assert(0 <= val)
    }
}
