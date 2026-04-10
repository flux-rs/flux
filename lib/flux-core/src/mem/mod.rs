use flux_attrs::*;

#[extern_spec(core::mem)]
#[spec(fn() -> usize[T::size_of()])]
fn size_of<T>() -> usize;

#[extern_spec(core::mem)]
#[spec(fn() -> usize[T::align_of()])]
fn align_of<T>() -> usize;
