// From nilehmann's `const_trait_default` example on PR #1733.
//
// A `#[constant]` annotation on a trait constant's *default*. `Inherit<T>` does not override
// `C`, so normalization uses the trait's annotated default instantiated at `Self := Inherit<T>`:
// `Self::width() == 0` becomes `1 == 0`, i.e. `false`, so `m` must return `10 < v`.
//
// (The refinement is called `width` rather than `size_of`, which would be ambiguous with the
// builtin `Sized::size_of` because of the `Sized` supertrait.)

use flux_attrs::*;

#[assoc(fn width() -> int)]
pub trait Tr: Sized {
    #[constant(Self::width() == 0)]
    const C: bool = size_of::<Self>() == 0;

    #[spec(fn() -> u32{v: if Self::C { v == 0 } else { 10 < v }})]
    fn m() -> u32;
}

pub struct Inherit<T>(T);

#[assoc(fn width() -> int { 1 })]
impl<T> Tr for Inherit<T> {
    #[spec(fn() -> u32{v: if Self::C { v == 0 } else { 10 < v }})]
    fn m() -> u32 {
        100
    }
}
