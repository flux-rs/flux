#[path = "../../lib/rvec.rs"]
mod rvec;

use rvec::RVec;

#[flux::refined_by(size:int)]
pub struct Bob {
    #[flux::field(RVec<i32{v: v >= 0}>[@size])]
    elems: RVec<i32>,
}

#[flux::sig(fn(&mut Bob{v: v.size > 0}) -> ())]
pub fn test(bob: &mut Bob) {
    bob.elems[0] = 0;
}
