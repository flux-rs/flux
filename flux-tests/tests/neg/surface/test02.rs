#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn() -> usize{v: v > 0})]
pub fn vec_push() -> usize {
    let mut v = RVec::new();
    v.push(1);
    v.push(2);
    let r = &mut v[2]; //~ ERROR precondition might not hold
    *r
}
