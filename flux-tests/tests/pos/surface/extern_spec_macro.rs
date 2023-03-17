// ignore-test
// Need to add macros to test
#![feature(register_tool)]
#![register_tool(flux)]

use std::mem::swap;

#[extern_spec]
#[flux::sig(fn(&mut i32[@a], &mut i32{v : a < v }) -> ())]
fn swap(a: &mut i32, b: &mut i32);

pub fn test() {
  let mut x = 1;
  let mut y = 2;
  swap(&mut x, &mut y);
}
