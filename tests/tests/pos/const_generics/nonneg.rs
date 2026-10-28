// A `const N: usize` generic gets the same invariants as an ordinary `usize` value (`0 <= N`).
// Each `const_*` function has an `arg_*` twin using an ordinary `n: usize` argument instead.

use flux_attrs::*;

// 1. Returning `N` as a `usize` with a non-negativity postcondition.

#[spec(fn() -> usize{v: 0 <= v})]
pub fn const_nonneg<const N: usize>() -> usize {
    N
}

#[spec(fn(n: usize) -> usize{v: 0 <= v})]
pub fn arg_nonneg(n: usize) -> usize {
    n // ok
}

// 2. A struct invariant `len <= N`, established by `len: 0`.

#[refined_by(len: int)]
#[invariant(len <= N)]
pub struct ConstBuf<const N: usize> {
    #[field(usize[len])]
    len: usize,
}

pub fn const_empty<const N: usize>() -> ConstBuf<N> {
    ConstBuf { len: 0 }
}

#[refined_by(len: int, cap: int)]
#[invariant(len <= cap)]
pub struct ArgBuf {
    #[field(usize[len])]
    len: usize,
    #[field(usize[cap])]
    cap: usize,
}

pub fn arg_empty(n: usize) -> ArgBuf {
    ArgBuf { len: 0, cap: n } // ok
}

// 3. `N - 1` after ruling out `N == 0`.

pub fn const_last<const N: usize>() -> usize {
    if N == 0 {
        return 0;
    }
    N - 1
}

pub fn arg_last(n: usize) -> usize {
    if n == 0 {
        return 0;
    }
    n - 1 // ok
}
