#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(
fn(&mut RVec<i32{v : v >= 0}>[@n]) -> i32[0]
requires n > 0
)]
pub fn pledge00(vec: &mut RVec<i32>) -> i32 {
    vec[0] = -1; //~ ERROR refinement type error
    0
}
