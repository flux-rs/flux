#![allow(unused_attributes)]
#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/surface/rvec.rs"]
pub mod rvec;
use rvec::RVec;

#[lr::sig(fn(src: & n@RVec<i32>, dst: &mut RVec<i32>[n]) -> i32; dst: RVec<i32>[n])]
fn bcopy_aux(src: &RVec<i32>, dst: &mut RVec<i32>) -> i32 {
  let mut i = 0;
  let n = src.len();
  while i < n {
    let r = dst.get_mut(i);
    *r = *src.get(i);
    i += 1;
  }
  0
}

#[lr::sig(fn(src: & n@RVec<i32>) -> RVec<i32>[n])]
pub fn bcopy(src: &RVec<i32>) -> RVec<i32> {
  let sz = src.len();
  let mut dst = RVec::from_elem_n(0, sz);
  bcopy_aux(src, &mut dst);
  dst
}
