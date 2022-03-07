#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/surface/rvec.rs"]
mod rvec;
use rvec::RVec;

#[lr::sig(fn(vec: &mut n@RVec<i32{v : v >= 0}>{n > 0}) -> i32[0]; vec: RVec<i32{v : v >= 0}>[n])]
pub fn pledge00(vec: &mut RVec<i32>) -> i32 { //~ ERROR postcondition might not hold
    let r;
    r = vec.get_mut(0);
    *r = -1;
    0
}
