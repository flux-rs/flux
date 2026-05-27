#![allow(unused)]

extern crate flux_alloc;
extern crate flux_core;

#[flux_rs::sig(fn(&[u8][@n]) -> Vec<u8>[n])]
fn test1(s: &[u8]) -> Vec<u8> {
    s.to_vec()
}

#[flux_rs::sig(fn(&mut [u8][@n]) -> Vec<u8>[n])]
fn test1_mut(s: &mut [u8]) -> Vec<u8> {
    s.to_vec()
}

#[flux_rs::sig(fn(&Vec<u8>[@n]) -> Vec<u8>[n])]
fn test2(s: &Vec<u8>) -> Vec<u8> {
    s.clone()
}

#[flux_rs::sig(fn(&[u8][@n]) -> Vec<u8>[n])]
fn test3(s: &[u8]) -> Vec<u8> {
    s.to_vec().clone()
}

#[flux_rs::sig(fn(&Vec<u8>[@n], &[u8][n]))]
fn lib4(v: &Vec<u8>, s: &[u8]) {}

fn test4(v: &Vec<u8>) {
    let s = &v;
    lib4(v, s);
}

#[flux_rs::sig(fn(&mut [u8][100]))]
pub fn lib4_mut(_s: &mut [u8]) {}

#[flux_rs::sig(fn(Vec<u8>[100]))]
pub fn test4_mut(mut v: Vec<u8>) {
    let s = &mut v;
    lib4_mut(s);
}
