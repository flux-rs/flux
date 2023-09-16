#![feature(register_tool)]
#![register_tool(flux)]

use std::slice::from_ref;

use flux_rs::extern_spec;

#[extern_spec]
#[flux::sig(fn(&T) -> &[T][1])]
fn from_ref<T>(s: &T) -> &[T];

#[flux::sig(fn(&i32) -> &[i32]{n: n > 1})]
pub fn test(x: &i32) -> &[i32] {
    from_ref(x) //~ ERROR refinement type
}
