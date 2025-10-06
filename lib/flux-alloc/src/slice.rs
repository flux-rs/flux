use std::alloc::Allocator;

use flux_attrs::*;

#[extern_spec]
impl<T> [T] {
    #[spec(fn(self: Box<[T][@n], A>) -> Vec<T, A>[n])]
    fn into_vec<A>(self: Box<[T], A>) -> Vec<T, A>
    where
        A: Allocator;
}
