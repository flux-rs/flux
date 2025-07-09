use flux_rs::{assert, attrs::*};
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
        d[0] = 10;
    }
}

// pub fn copy_to_slice(src: &[u8], dest: &mut [u8]) {
//     let src_len = src.len();
//     let dest_len = dest.len();
//     if src_len == dest_len {
//         for (i, b) in src.iter().enumerate() {
//             assert(i < src_len);
//             assert(i < dest_len);
//             dest[i] = *b;
//         }
//     }
// }
