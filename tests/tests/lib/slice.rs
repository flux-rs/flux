use std::slice::Iter;

use flux_rs::extern_spec;

// Spec for slice
#[extern_spec]
impl<T> [T] {
    #[flux::sig(fn(&[T][@n]) -> usize[n])]
    fn len(v: &[T]) -> usize;

    #[flux::sig(fn(&[T][@n]) -> Iter<T>[0, n])]
    fn iter(v: &[T]) -> Iter<'_, T>;
}
