#[cfg(flux)]
use core::ops::Index;

use flux_attrs::*;

#[extern_spec(core::array)]
impl<T, I, const N: usize> Index<I> for [T; N]
where
    [T]: Index<I>,
{
    #![assoc(
        fn in_bounds(len: (), idx: I) -> bool {
            <[T] as Index<I>>::in_bounds(N, idx)
        }

        fn output_pred(len: (), idx: I, out: <[T] as Index<I>>::Output) -> bool {
            <[T] as Index<I>>::output_pred(N, idx, out)
        }
    )]

    #[sig(fn(&Self, {I[@idx] | <[T] as Index<I>>::in_bounds(N, idx)}) -> &<[T; N] as Index<I>>::Output{out: <[T] as Index<I>>::output_pred(N, idx, out)})]
    fn index(&self, index: I) -> &<[T; N] as Index<I>>::Output;
}
