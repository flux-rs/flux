#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::{RVec, rslice::RSlice};

#[flux::sig(fn(&mut RVec<T>[10]))]
fn test00<T>(vec: &mut RVec<T>) {
    let mut s = RSlice::from_vec(vec);
    let s1 = s.subslice(0, 3);
    let s2 = s.subslice(4, 5);
}

#[flux::trusted]
#[flux::sig(fn(x: &[T][@n]) -> usize[n])]
fn len<T>(x: &[T]) -> usize {
    x.len()
}

#[flux::sig(fn(&mut [i32][@n], &[i32][n]))]
fn add(x: &mut [i32], y: &[i32]) {
    let mut i = 0;
    while i < len(x) {
        x[i] += y[i];
        i += 1;
    }
}

#[flux::sig(fn(&mut {RVec<i32>[@n] | n % 2 == 0 && n > 0}))]
fn test01(vec: &mut RVec<i32>) {
    let n = vec.len();
    let mut s = RSlice::from_vec(vec);
    let mut s1 = s.subslice(0, n / 2 - 1);
    let s2 = s.subslice(n / 2, n - 1);
    add(s1.as_mut_slice(), s2.as_slice())
}
