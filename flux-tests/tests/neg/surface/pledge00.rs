#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/surface/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(
fn(&mut RVec<i32{v : v >= 0}>[@n]) -> i32[0]
requires n > 0
)]
pub fn pledge00(vec: &mut RVec<i32>) -> i32 {
    let r;
    r = vec.get_mut(0); //~ ERROR precondition might not hold
    *r = -1;
    0
}
