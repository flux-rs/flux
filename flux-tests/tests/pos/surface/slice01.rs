#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(arr: &[i32][@n], i:usize{0 <= i && i < n}) -> i32)]
pub fn foo(arr: &[i32], i: usize) -> i32 {
    arr[i]
}
