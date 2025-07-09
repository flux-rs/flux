use flux_rs::attrs::*;
extern crate flux_core;

pub fn silly_slice(_src: &mut [i32]) -> usize {
    12
}

pub fn mickey(n: usize) -> usize {
    n + 1
}

#[spec(fn(src: &mut [i32][12]))]
pub fn blob(src: &mut [i32]) {
    let _k = silly_slice(src);
    let _n = mickey(5);
}

pub fn test00(s: &[i32]) -> i32 {
    let n = s.len();
    if n > 0 {
        let tmp = s[0];
        tmp
    } else {
        0
    }
}

pub fn test01(s: &mut [i32]) -> i32 {
    let n = s.len();
    if n > 0 {
        let tmp = s[0];
        tmp
    } else {
        0
    }
}

pub fn blah(d: &mut [i32]) {
    if d.len() > 0 {
        d[0] = 10; //~ ERROR assertion might fail
    }
}
