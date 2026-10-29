//! Const generics of a method are scoped to that method: sibling methods in the same impl or trait
//! can reuse the same name without clashing.

pub struct S;

impl S {
    #[flux::sig(fn() -> usize[N])]
    pub fn foo<const N: usize>() -> usize {
        N
    }

    #[flux::sig(fn() -> usize[N])]
    pub fn bar<const N: usize>() -> usize {
        N
    }
}

pub trait Tr {
    #[flux::sig(fn() -> usize[N])]
    fn foo<const N: usize>() -> usize;

    #[flux::sig(fn() -> usize[N])]
    fn bar<const N: usize>() -> usize;
}
