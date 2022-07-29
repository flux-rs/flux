#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(
fn(&mut RVec<i32>[@n], b:bool) -> i32[0]
requires 2 <= n
)]
pub fn test1(vec: &mut RVec<i32>, b: bool) -> i32 {
    let r;
    if b {
        r = &mut vec[0];
    } else {
        r = &mut vec[1];
    }
    *r = 12;
    0
}
