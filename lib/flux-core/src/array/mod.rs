#[cfg(flux)]
use core::ops;
use core::ops::Index;

use flux_attrs::*;

#[extern_spec(core::array)]
// impl<T, I, const N: usize> const Index<I> for [T; N]
impl<T, I, const N: usize> Index<I> for [T; N]
where
    [T]: Index<I>,
    // ORIG: [T]: [const] Index<I>,
{
    // OK but lame #[sig(fn(&Self, {I[@idx] | <[T] as Index<I>>::in_bounds(N, idx)}) -> &<[T; N] as Index<I>>::Output{out: <[T] as Index<I>>::output_pred(N, idx, out)})]
    #[sig(fn(&Self, {I[@idx] | <[T] as Index<I>>::in_bounds(N, idx)}) -> &<[T;_ ] as Index<I>>::Output{out: <[T] as Index<I>>::output_pred(N, idx, out)})]
    fn index(&self, index: I) -> &<[T; N] as Index<I>>::Output;
}

#[cfg(flux_sysroot_test)]
mod tests {
    #![allow(dead_code)]

    use flux_attrs::*;

    fn test00(xs: &[i32; 100]) {
        let _y = &xs[0..1];
    }

    #[should_fail]
    fn test01(xs: &[i32; 10]) {
        let _y = &xs[0..20];
    }
}
