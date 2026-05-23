use std::ops::Index;
extern crate flux_core;

pub struct Foo<T, I, const N: usize>(T, I, [T; N]);

impl<T, I, const N: usize> Foo<T, I, N>
where
    [T]: Index<I>,
{
    #[flux::sig(fn(_, _) -> &<[T;N] as Index<I>>::Output{out: true})]
    pub fn index_crash(_self: &[T; N], _index: I) -> &<[T; N] as Index<I>>::Output {
        panic!()
    }
}
