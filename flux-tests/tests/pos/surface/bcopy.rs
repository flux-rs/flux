#![allow(unused_attributes)]
#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
pub mod rvec;
use rvec::RVec;

#[flux::sig(fn(&RVec<i32>[@n], &mut RVec<i32>[n]) -> i32)]
fn bcopy_aux(src: &RVec<i32>, dst: &mut RVec<i32>) -> i32 {
    let mut i = 0;
    let n = src.len();
    while i < n {
        dst[i] = src[i];
        i += 1;
    }
    0
}

#[flux::sig(fn(&RVec<i32>[@n]) -> RVec<i32>[n])]
pub fn bcopy(src: &RVec<i32>) -> RVec<i32> {
    let sz = src.len();
    let mut dst = RVec::from_elem_n(0, sz);
    bcopy_aux(src, &mut dst);
    dst
}
