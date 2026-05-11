#![allow(unused)]

#[flux_rs::sig(fn() -> i32[10])]
fn mk_ten() -> i32 {
    let my_slice: [u8; 5] = [1, 2, 3, 4, 5];
    let subslice = &my_slice[2..4];

    let n = subslice[0]; // assertion might fail: possible out-of-bounds access
    let m = subslice[1]; // assertion might fail: possible out-of-bounds access
    10
}