// Negative version of pos/surface/assoc_const08.rs: the inherited default `C` is `false`, so
// `m` must return a value greater than `10`.

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
        5 //~ ERROR refinement type
    }
}

// `Override<T>` overrides `C` without an annotation, with a body we can't evaluate, so `C` must
// stay opaque: in particular we must not fall back to the trait's annotated default.
pub struct Override<T>(T);

#[assoc(fn width() -> int { 1 })]
impl<T> Tr for Override<T> {
    const C: bool = size_of::<T>() == 0;

    #[spec(fn() -> u32{v: if Self::C { v == 0 } else { 10 < v }})]
    fn m() -> u32 {
        100 //~ ERROR refinement type
    }
}
