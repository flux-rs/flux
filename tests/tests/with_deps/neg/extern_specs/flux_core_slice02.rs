#![allow(unused)]
extern crate flux_core;

#[flux_rs::sig(fn(&[u8; N]) requires 4 <= N)]
fn create_range<const N: usize>(arr: &[u8; N]) {
    let s = &arr[2..8]; //~ ERROR refinement type error
}

#[flux_rs::sig(fn(&[u8; N]) requires 4 <= N)]
fn create_range_to<const N: usize>(arr: &[u8; N]) {
    let s = &arr[..8]; //~ ERROR refinement type error
}

#[flux_rs::sig(fn(&[u8; N]) requires 4 <= N)]
fn create_range_from<const N: usize>(arr: &[u8; N]) {
    let s = &arr[8..]; //~ ERROR refinement type error
}

#[flux_rs::sig(fn(&[u8; N]) requires 4 <= N)]
fn access_range<const N: usize>(arr: &[u8; N]) {
    let s = &arr[2..4];
    flux_rs::assert(s.len() == 2);
    let _ = s[2]; //~ ERROR assertion might fail
}

#[flux_rs::sig(fn(&[u8; N]) requires 4 <= N)]
fn access_range_to<const N: usize>(arr: &[u8; N]) {
    let s = &arr[..3];
    flux_rs::assert(s.len() == 3);
    let _ = s[3]; //~ ERROR assertion might fail
}

#[flux_rs::sig(fn(&[u8; N]) requires 4 <= N)]
fn access_range_from<const N: usize>(arr: &[u8; N]) {
    let s = &arr[2..];
    flux_rs::assert(s.len() == arr.len() - 2);
    let _ = s[2]; //~ ERROR assertion might fail
}
