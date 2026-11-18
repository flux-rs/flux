// From nilehmann's `assoc_const_generics` example on PR #1733.
//
// An associated constant defined as a const generic of the impl, `const LEN: usize = N`. Const
// evaluation reports `TooGeneric`, so the value comes from the `#[constant(N)]` annotation:
// `<Arr<N> as Len>::LEN` normalizes to the const generic `N`, the same symbol the body's `N` is
// refined to. At `Arr<3>` the instantiated value is the literal `3`.

use flux_attrs::*;

pub trait Len {
    const LEN: usize;

    #[spec(fn() -> usize[Self::LEN])]
    fn len() -> usize;
}

pub struct Arr<const N: usize>;

impl<const N: usize> Len for Arr<N> {
    #[constant(N)]
    const LEN: usize = N;

    #[spec(fn() -> usize[Self::LEN])]
    fn len() -> usize {
        N
    }
}

#[spec(fn() -> usize[3])]
pub fn test() -> usize {
    <Arr<3> as Len>::len()
}
