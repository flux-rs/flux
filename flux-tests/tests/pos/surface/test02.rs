#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/surface/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn() -> usize{v: v > 0})]
pub fn vec_push() -> usize {
    let mut v = RVec::new();
    v.push(1);
    v.push(2);
    let r = v.get_mut(1);
    *r
}
