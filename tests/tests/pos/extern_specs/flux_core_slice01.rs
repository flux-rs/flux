#![allow(unused)]

extern crate flux_core;

#[flux_rs::sig(fn(&[u8]{n: n >= 4}))]
fn foo(arr: &[u8]) {
    // Range
    let s1 = &arr[2..4];
    flux_rs::assert(s1.len() == 2);
    let _ = s1[0];
    let _ = s1[1];

    // RangeTo
    let s2 = &arr[..3];
    flux_rs::assert(s2.len() == 3);
    let _ = s2[0];
    let _ = s2[2];

    // RangeFrom
    let s3 = &arr[2..];
    flux_rs::assert(s3.len() == arr.len() - 2);
    let _ = s3[0];
    let _ = s3[1];
}
