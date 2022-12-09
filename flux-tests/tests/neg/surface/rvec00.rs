#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn() -> RVec<i32>[1])]
pub fn vec_empty() -> RVec<i32> {
    let mut mv = rvec![];
    mv.push(1);
    mv
}

pub fn vec_push() -> usize {
    let v = rvec![0, 1];
    let r = v[0];
    let r = r + v[1];
    let r = r + v[2]; //~ ERROR precondition might not hold
    r
}
