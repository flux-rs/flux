// From nilehmann's `assoc_const_nested` example on PR #1733.
//
// An associated constant defined as another trait constant, `const C: usize = T::C`. Const
// evaluation reports `TooGeneric`, so the value comes from the `#[constant(T::C)]` annotation:
// `<Wrap<T> as Tr>::C` normalizes to `<T as Tr>::C`, exactly the symbol `T::get()` is refined
// with. At `Wrap<Base>` it further normalizes to `5`.

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
        T::get()
    }
}

#[spec(fn() -> usize[5])]
pub fn test() -> usize {
    <Wrap<Base> as Tr>::get()
}
