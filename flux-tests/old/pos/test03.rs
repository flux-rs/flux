#![feature(register_tool)]
#![register_tool(flux)]

#[flux::ty(fn<n: int>(l: i32@n; ref<l>) -> i32; l: i32 @ {n+1})]
pub fn inc(x: &mut i32) -> i32 {
    *x += 1;
    0
}
