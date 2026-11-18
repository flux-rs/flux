// Negative version of pos/surface/assoc_const05.rs: `Self::LEN` is `N`, not `N + 1`, and
// `<Arr<4> as Len>::LEN` is `4`, not `3`.

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
        N + 1 //~ ERROR refinement type
    }
}

#[spec(fn() -> usize[3])]
pub fn test() -> usize {
    <Arr<4> as Len>::len() //~ ERROR refinement type
}
