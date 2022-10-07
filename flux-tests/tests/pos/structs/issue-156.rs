#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;

use rvec::RVec;

pub struct Bob {
    #[flux::field(RVec<i32>{n:n>0})]
    elems: RVec<i32>,
}

#[flux::sig(fn(Bob) -> ())]
pub fn test(bob: Bob) {
    let _x = bob.elems[0];
}
