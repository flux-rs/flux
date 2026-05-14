use flux_attrs::*;

#[extern_spec(core::mem)]
#[spec(fn() -> usize[T::size_of()])]
fn size_of<T>() -> usize;

#[extern_spec(core::mem)]
#[spec(fn() -> usize[T::align_of()])]
fn align_of<T>() -> usize;

/// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/mem/maybe_uninit.rs#L346
#[extern_spec(core::mem)]
#[refined_by(init: bool)]
struct MaybeUninit<T>;

#[extern_spec(core::mem)]
impl<T: Copy> MaybeUninit<T> {
    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/mem/maybe_uninit.rs#L420
    #[no_panic]
    #[sig(fn() -> MaybeUninit<T>[false])]
    fn uninit() -> MaybeUninit<T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/mem/maybe_uninit.rs#L564
    #[no_panic]
    #[sig(fn(self: &mut MaybeUninit<T>, T) -> &mut T
          ensures self: MaybeUninit<T>[true])]
    fn write(&mut self, val: T) -> &mut T;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/mem/maybe_uninit.rs#L704
    #[no_panic]
    #[sig(fn(MaybeUninit<T>[true]) -> T)]
    unsafe fn assume_init(self) -> T;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/mem/maybe_uninit.rs#L876
    #[no_panic]
    #[sig(fn(&MaybeUninit<T>[true]) -> &T)]
    unsafe fn assume_init_ref(&self) -> &T;
}
