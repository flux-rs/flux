use flux_attrs::*;

#[extern_spec(core::ptr)]
#[refined_by(p: ptr)]
#[invariant(p.addr != 0)]
struct NonNull<T>;

#[extern_spec(core::ptr)]
impl<T> NonNull<T> {
    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L234
    #[spec(fn(*mut[@p] T) -> NonNull<T>[p] requires p.addr != 0)]
    unsafe fn new_unchecked(ptr: *mut T) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L270
    #[spec(fn(*mut[@p] T) -> Option<NonNull<T>[p]>)]
    fn new(ptr: *mut T) -> Option<NonNull<T>>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L402
    #[spec(fn(NonNull<T>[@nn]) -> *mut[nn] T)]
    fn as_ptr(self) -> *mut T;
}
