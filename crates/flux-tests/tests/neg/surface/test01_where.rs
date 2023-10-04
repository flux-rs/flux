#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(
fn(&mut RVec<i32>[@n], bool) -> i32[0]
requires 1 <= n
)]
pub fn test1(vec: &mut RVec<i32>, b: bool) -> i32 {
    let r;
    if b {
        r = &mut vec[0];
    } else {
        r = &mut vec[1]; //~ ERROR refinement type error
    }
    *r = 12;
    0
}
