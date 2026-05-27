use std::alloc::Allocator;

use flux_attrs::*;

#[extern_spec]
impl<T> [T] {
    #[spec(fn(self: Box<[T][@n], A>) -> Vec<T, A>[n])]
    fn into_vec<A>(self: Box<[T], A>) -> Vec<T, A>
    where
        A: Allocator;

    #[spec(fn(self: &[T][@n]) -> Vec<T>[n])]
    fn to_vec(self: &[T]) -> Vec<T>
    where
        T: Clone;
}
