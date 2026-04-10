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

    /// Delegates to `SliceIndex::index`, documented as panicking iff out of
    /// bounds, so `#[no_panic]` is sound under the `in_bounds` precondition.
    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/slice/index.rs#L15
    #[no_panic]
    #[sig(fn(&Self[@len], {I[@idx] | <Self as ops::Index<I>>::in_bounds(len, idx)}) -> &I::Output)]
    fn index(&self, index: I) -> &I::Output;
}

#[extern_spec(core::slice)]
impl<T, I: SliceIndex<[T]>> ops::IndexMut<I> for [T] {
    /// See `index`. Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/slice/index.rs#L26
    #[no_panic]
    #[sig(fn(&mut Self[@len], {I[@idx] | <Self as ops::Index<I>>::in_bounds(len, idx)}) -> &mut I::Output)]
    fn index_mut(&mut self, index: I) -> &mut I::Output;
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
