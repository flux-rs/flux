#![allow(unused)]

extern crate flux_core;

#[flux_rs::sig(fn(&[u8]{n: n >= 4}) -> i32[10])]
fn foo(arr: &[u8]) -> i32 {
    let subslice = &arr[2..4];
    let _ = subslice[0]; // ok!
    let _ = subslice[1]; // ok!
    10
}
