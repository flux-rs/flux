use flux_rs::{assert, attrs::*};
extern crate flux_core;
use std::ops::Index;

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

//---

struct Foo<T, I, const N: usize>(T, I, [T; N])
where
    [T]: Index<I>;

impl<T, I, const N: usize> Foo<T, I, N>
where
    [T]: Index<I>,
{
    // #[flux::sig(fn(&Self, {I[@idx] | <[T] as Index<I>>::in_bounds(N, idx)}) -> &<[T;_] as Index<I>>::Output{out: <[T] as Index<I>>::output_pred(N, idx, out)})]
    // CRASH #[flux::sig(fn(_self: &[T; _], idx: I) -> &<[T;_] as Index<I>>::Output{out: <[T;_ ] as Index<I>>::output_pred(N, idx, out)})]
    // OK #[flux::sig(fn(_self: &[T; _], idx: I) -> &<[T;_] as Index<I>>::Output)]
    // OK #[flux::sig(fn(_self: &[T; _],{I[@idx] | <[T] as Index<I>>::in_bounds(N, idx)}) -> &<[T;_] as Index<I>>::Output)]
    #[flux::sig(fn(_self: &[T; _],{I[@idx] | <[T] as Index<I>>::in_bounds(N, idx)}) -> &<[T;_] as Index<I>>::Output{out:<[T] as Index<I>>::output_pred(N, idx, out) })]
    pub fn index(_self: &[T; N], _index: I) -> &<[T; N] as Index<I>>::Output {
        panic!() // <[T; N] as Index<I>>::index(__self, index)
    }
}
