#[cfg(flux)]
use core::ops;

use flux_attrs::*;

#[extern_spec(core::slice)]
impl<T, I: SliceIndex<[T]>> ops::Index<I> for [T] {
    #![assoc(
        fn in_bounds(len: int, idx: I) -> bool {
            <I as SliceIndex<[T]>>::in_bounds(idx, len)
        }
    )]

    #[sig(fn(&Self[@len], {I[@idx] | <Self as ops::Index<I>>::in_bounds(len, idx)}) -> &I::Output)]
    fn index(&self, index: I) -> &I::Output;
}

#[extern_spec(core::slice)]
trait SliceIndex<T> {
    #![assoc(fn in_bounds(idx: Self, v: T) -> bool { true })] //
}

#[extern_spec(core::slice)]
impl<T> SliceIndex<[T]> for usize {
    #![assoc(fn in_bounds(idx: int, len: int) -> bool { idx < len })] //
}

#[extern_spec(core::slice)]
impl<T> SliceIndex<[T]> for ops::Range<usize> {
    #![assoc(
        fn in_bounds(r: ops::Range<int>, len: int) -> bool {
            r.start <= r.end && r.end <= len
        }
    )] //
}

#[cfg(flux_sysroot_test)]
mod tests {
    #![allow(dead_code)]

    use flux_attrs::*;

    #[sig(fn(&[i32]{n: n > 10}))]
    fn test00(xs: &[i32]) {
        let _y = &xs[0..1];
    }

    #[should_fail]
    fn test01(xs: &[i32]) {
        let _y = &xs[0..1];
    }
}
