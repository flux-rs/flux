#![feature(register_tool)]
#![register_tool(flux)]

pub fn foo(arr: &[i32], i: usize) -> i32 {
    arr[i]
}
