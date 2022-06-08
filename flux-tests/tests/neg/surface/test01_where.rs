#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/surface/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(
fn(&mut RVec<i32>[@n], bool) -> i32[0]
requires 1 <= n
)]
pub fn test1(vec: &mut RVec<i32>, b: bool) -> i32 {
    let r;
    if b {
        r = vec.get_mut(0);
    } else {
        r = vec.get_mut(1); //~ ERROR precondition might not hold
    }
    *r = 12;
    0
}
