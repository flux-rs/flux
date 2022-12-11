#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::{rslice::RSlice, RVec};

#[flux::sig(fn(&mut RVec<T>[10]))]
fn test00<T>(vec: &mut RVec<T>) {
    let mut s = RSlice::from_vec(vec);
    let s1 = s.subslice(0, 3);
    let s2 = s.subslice(2, 5); //~ ERROR precondition
}
