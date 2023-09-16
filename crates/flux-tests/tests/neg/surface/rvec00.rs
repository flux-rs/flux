#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn() -> RVec<i32>[5])]
pub fn test1() -> RVec<i32> {
    rvec![ 12; 55 ] //~ ERROR refinement type
}

#[flux::sig(fn(n:usize) -> RVec<i32>[n + 1])]
pub fn test2(n: usize) -> RVec<i32> {
    rvec![ 12; n ] //~ ERROR refinement type
}

pub fn test3() -> usize {
    let v = rvec![0, 1];
    let r = v[0];
    let r = r + v[1];
    let r = r + v[2]; //~ ERROR refinement type error
    r
}
