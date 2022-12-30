#![feature(register_tool)]
#![register_tool(flux)]

pub fn foo(arr: &[i32], i: usize) -> i32 {
    arr[i] //~ ERROR assertion might fail
}

#[flux::trusted]
#[flux::sig(fn(arr: &[T][@n]) -> usize[n])]
fn len<T>(arr: &[T]) -> usize {
    arr.len()
}

#[flux::sig(fn(arr: &[i32][@n]) -> i32)]
pub fn bar(arr: &[i32]) -> i32 {
    let n = len(arr);
    if 0 < n {
        arr[10] //~ ERROR assertion might fail
    } else {
        0
    }
}
