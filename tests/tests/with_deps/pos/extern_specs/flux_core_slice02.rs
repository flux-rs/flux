#![allow(unused)]

extern crate flux_core;

#[flux_rs::sig(fn(&[u8; N]) requires N >= 4)]
fn foo<const N: usize>(arr: &[u8; N]) {
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

#[flux_rs::sig(fn(&mut [u8; N]) requires N >= 4)]
fn test_mut<const N: usize>(arr: &mut [u8; N]) {
    let n = arr.len();
    // Range
    let s1 = &mut arr[2..4];
    flux_rs::assert(s1.len() == 2);
    s1[0] = 0;
    s1[1] = 0;

    // RangeTo
    let s2 = &mut arr[..3];
    flux_rs::assert(s2.len() == 3);
    s2[0] = 0;
    s2[2] = 0;

    // RangeFrom
    let s3 = &mut arr[2..];
    flux_rs::assert(s3.len() == n - 2);
    s3[0] = 0;
    s3[1] = 0;
}
