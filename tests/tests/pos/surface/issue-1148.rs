#![allow(unused)]

use flux_rs::attrs::*;
extern crate flux_core;
#[refined_by(size: int, init: int)]
struct Uninit<'a, T> {
    #[field(&mut [_][size])]
    data: &'a mut [Option<T>],

    #[field(usize[init])]
    initialized_len: usize,
}

impl<'a, T> Uninit<'a, T> {
    // #[trusted]
    #[spec(fn(me: &mut Self[@size, @init], T)
           requires init < size
           ensures me: Self[size, init + 1])]
    fn push(&mut self, value: T) {
        self.data[self.initialized_len] = Some(value);
        self.initialized_len += 1;
    }
}

#[spec(fn(me: &mut Uninit<_>[@n, 0], other: &[_][n]) ensures me: Uninit<_>[n, n])]
fn fill(me: &mut Uninit<i32>, other: &[i32]) {
    let mut i = 0;
    while i < other.len() {
        me.push(other[i]);
        i += 1;
    }
    // TODO(RJ): use the below after #1170 and #1171 are merged
    // for item in other {
    //     me.push(*item);
    // }
}

#[spec(fn(me: &mut Uninit<_>) ensures me: Uninit<_>)]
fn bill(me: &mut Uninit<i32>) {}
