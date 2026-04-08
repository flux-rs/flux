mod index;
mod iter;

use flux_attrs::*;

#[extern_spec(core::slice)]
impl<T> [T] {
    #[no_panic]
    #[spec(fn(&Self[@n]) -> usize[n])]
    fn len(&self) -> usize;

    #[spec(fn(&Self[@n]) -> bool[n == 0])]
    fn is_empty(&self) -> bool;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L154
    #[spec(fn(&Self[@n]) -> Option<&T>[n != 0])]
    fn first(&self) -> Option<&T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L280
    #[no_panic]
    #[spec(fn(&Self[@n]) -> Option<&T>[n != 0])]
    fn last(&self) -> Option<&T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L570
    #[no_panic]
    #[spec(fn(&Self[@n], I[@idx]) -> Option<&I::Output>[<I as SliceIndex<[T]>>::in_bounds(idx, n)])]
    fn get<I: SliceIndex<[T]>>(&self, index: I) -> Option<&I::Output>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L197
    #[no_panic]
    #[spec(fn(&Self[@n]) -> Option<(&T, &[T][n - 1])>[n != 0])]
    fn split_first(&self) -> Option<(&T, &[T])>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L239
    #[no_panic]
    #[spec(fn(&Self[@n]) -> Option<(&T, &[T][n - 1])>[n != 0])]
    fn split_last(&self) -> Option<(&T, &[T])>;

    #[spec(fn(&Self[@n]) -> Iter<T>[0, n])]
    fn iter(&self) -> Iter<'_, T>;

    #[no_panic]
    #[spec(fn(&Self[@n], mid: usize{mid <= n}) -> (&[T][mid], &[T][n - mid]))]
    fn split_at(&self, mid: usize) -> (&[T], &[T]);

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/slice/mod.rs#L2185
    #[no_panic]
    #[spec(fn(&Self[@n], usize[@mid]) -> Option<(&[T][mid], &[T][n - mid])>[mid <= n])]
    fn split_at_checked(&self, mid: usize) -> Option<(&[T], &[T])>;

    #[spec(fn(&Self[@n]) -> *const{p: ptr_size(p) == n} T)]
    fn as_ptr(&self) -> *const T;

    #[spec(fn(&mut Self[@n]) -> *mut{p: ptr_size(p) == n} T)]
    fn as_mut_ptr(&mut self) -> *mut T;
}
