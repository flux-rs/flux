#[cfg(flux)]
use core::ops;

use flux_attrs::*;

#[extern_spec(core::slice)]
impl<T, I: SliceIndex<[T]>> ops::Index<I> for [T] {
    #![reft(
        fn in_bounds(len: int, idx: I) -> bool {
            <I as SliceIndex<[T]>>::in_bounds(idx, len)
        }
    )]

    #[sig(fn(&Self[@len], {I[@idx] | <Self as ops::Index<I>>::in_bounds(len, idx)}) -> &I::Output)]
    fn index(&self, index: I) -> &I::Output;
}

#[extern_spec(core::slice)]
trait SliceIndex<T> {
    #![reft(fn in_bounds(idx: Self, v: T) -> bool { true })] //
}

#[extern_spec(core::slice)]
impl<T> SliceIndex<[T]> for usize {
    #![reft(fn in_bounds(idx: int, len: int) -> bool { idx < len })] //
}

