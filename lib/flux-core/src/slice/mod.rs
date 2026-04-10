//! Extern specs for [`core::slice`].
//!
//! # Soundness of `SliceIndex`-based annotations
//!
//! Several annotations rely on [`SliceIndex`] being a sealed trait: it
//! requires `private_slice_index::Sealed`, which has no public path outside of
//! `core`, so its set of implementations is fixed and exhaustive. The sealed implementations
//! were inspected to ensure these specs are sound.
// Perhaps one day we can properly verify them with Flux.

mod index;
mod iter;

use flux_attrs::*;

#[extern_spec(core::slice)]
impl<T> [T] {
    #[no_panic]
    #[spec(fn(&Self[@n]) -> usize[n])]
    fn len(&self) -> usize;

    #[no_panic]
    #[spec(fn(&Self[@n]) -> bool[n == 0])]
    fn is_empty(&self) -> bool;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L154
    #[no_panic]
    #[spec(fn(&Self[@n]) -> Option<&T>[n != 0])]
    fn first(&self) -> Option<&T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L177
    #[no_panic]
    #[spec(fn(&mut Self[@n]) -> Option<&mut T>[n != 0])]
    fn first_mut(&mut self) -> Option<&mut T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L280
    #[no_panic]
    #[spec(fn(&Self[@n]) -> Option<&T>[n != 0])]
    fn last(&self) -> Option<&T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L303
    #[no_panic]
    #[spec(fn(&mut Self[@n]) -> Option<&mut T>[n != 0])]
    fn last_mut(&mut self) -> Option<&mut T>;

    /// Delegates to `SliceIndex::get`. All sealed impls return `None` out of
    /// bounds (never panic), and `Some` iff `in_bounds` holds.
    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L570
    #[no_panic]
    #[spec(fn(&Self[@n], I[@idx]) -> Option<&I::Output>[<I as SliceIndex<[T]>>::in_bounds(idx, n)])]
    fn get<I: SliceIndex<[T]>>(&self, index: I) -> Option<&I::Output>;

    /// See `get`. Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L596
    #[no_panic]
    #[spec(fn(&mut Self[@n], I[@idx]) -> Option<&mut I::Output>[<I as SliceIndex<[T]>>::in_bounds(idx, n)])]
    fn get_mut<I: SliceIndex<[T]>>(&mut self, index: I) -> Option<&mut I::Output>;

    /// Delegates to `SliceIndex::get_unchecked`. `SliceIndex` documents calling
    /// with an out-of-bounds index as UB; `in_bounds` encodes that contract.
    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L635
    #[no_panic]
    #[spec(fn(&Self[@n], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, n)}) -> &I::Output)]
    unsafe fn get_unchecked<I: SliceIndex<[T]>>(&self, index: I) -> &I::Output;

    /// See `get_unchecked`. Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L679
    #[no_panic]
    #[spec(fn(&mut Self[@n], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, n)}) -> &mut I::Output)]
    unsafe fn get_unchecked_mut<I: SliceIndex<[T]>>(&mut self, index: I) -> &mut I::Output;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L197
    #[no_panic]
    #[spec(fn(&Self[@n]) -> Option<(&T, &[T][n - 1])>[n != 0])]
    fn split_first(&self) -> Option<(&T, &[T])>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L239
    #[no_panic]
    #[spec(fn(&Self[@n]) -> Option<(&T, &[T][n - 1])>[n != 0])]
    fn split_last(&self) -> Option<(&T, &[T])>;

    #[no_panic]
    #[spec(fn(&Self[@n]) -> Iter<T>[0, n])]
    fn iter(&self) -> Iter<'_, T>;

    #[no_panic]
    #[spec(fn(&Self[@n], mid: usize{mid <= n}) -> (&[T][mid], &[T][n - mid]))]
    fn split_at(&self, mid: usize) -> (&[T], &[T]);

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L2018
    #[no_panic]
    #[spec(fn(&mut Self[@n], mid: usize{mid <= n}) -> (&mut [T][mid], &mut [T][n - mid]))]
    fn split_at_mut(&mut self, mid: usize) -> (&mut [T], &mut [T]);

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L2185
    #[no_panic]
    #[spec(fn(&Self[@n], usize[@mid]) -> Option<(&[T][mid], &[T][n - mid])>[mid <= n])]
    fn split_at_checked(&self, mid: usize) -> Option<(&[T], &[T])>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L2224
    #[no_panic]
    #[spec(fn(&mut Self[@n], usize[@mid]) -> Option<(&mut [T][mid], &mut [T][n - mid])>[mid <= n])]
    fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut [T], &mut [T])>;

    #[no_panic]
    #[spec(fn(&Self[@n]) -> *const{p: ptr_size(p) == n} T)]
    fn as_ptr(&self) -> *const T;

    #[no_panic]
    #[spec(fn(&mut Self[@n]) -> *mut{p: ptr_size(p) == n} T)]
    fn as_mut_ptr(&mut self) -> *mut T;
}
