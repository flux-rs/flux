use std::{
    alloc::{Allocator, Global},
    ops::Deref,
    rc::Rc,
};

use flux_attrs::*;

#[extern_spec]
#[refined_by(inner: T)]
struct Rc<T, A: Allocator = Global>;

#[extern_spec]
impl<T, A: Allocator> Deref for Rc<T, A> {
    #[spec(fn (&Self[@me]) -> &T[me.inner])]
    fn deref(&self) -> &T;
}

#[extern_spec]
impl<T, A: Allocator + Clone> Clone for Rc<T, A> {
    #[spec(fn (&Self[@me]) -> Self[me.inner])]
    fn clone(&self) -> Self;
}

#[extern_spec]
impl<T> Rc<T> {
    #[spec(fn(T[@a]) -> Self[a])]
    fn new(value: T) -> Self;
}
