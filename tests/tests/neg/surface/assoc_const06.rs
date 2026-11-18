// Negative version of pos/surface/assoc_const06.rs: `Self::C` is `T::C`, not `T::C + 1`, and
// `<Wrap<Base> as Tr>::C` is `5`, not `6`.

use flux_attrs::*;

pub trait Tr {
    const C: usize;

    #[spec(fn() -> usize[Self::C])]
    fn get() -> usize;
}

pub struct Base;

impl Tr for Base {
    const C: usize = 5;

    #[spec(fn() -> usize[Self::C])]
    fn get() -> usize {
        5
    }
}

pub struct Wrap<T>(T);

impl<T: Tr> Tr for Wrap<T> {
    #[constant(T::C)]
    const C: usize = T::C;

    #[spec(fn() -> usize[Self::C])]
    fn get() -> usize {
        T::get() + 1 //~ ERROR refinement type
    }
}

#[spec(fn() -> usize[5])]
pub fn test() -> usize {
    <Wrap<Base> as Tr>::get() + 1 //~ ERROR refinement type
}
