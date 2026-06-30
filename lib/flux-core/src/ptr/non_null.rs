use flux_attrs::*;

#[extern_spec(core::ptr)]
#[refined_by(base: int, addr: int, size: int)]
#[invariant(addr != 0)]
struct NonNull<T>;

#[extern_spec(core::ptr)]
impl<T> NonNull<T> {
    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L234
    #[spec(fn(*mut[@p] T) -> NonNull<T>[p.base, p.addr, p.size] requires p.addr != 0)]
    unsafe fn new_unchecked(ptr: *mut T) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L270
    #[spec(fn(*mut[@p] T) -> Option<NonNull<T>[p.base, p.addr, p.size]>)]
    fn new(ptr: *mut T) -> Option<NonNull<T>>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L402
    #[spec(fn(NonNull<T>[@base, @addr, @size]) -> *mut[base, addr, size] T)]
    fn as_ptr(self) -> *mut T;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L652
    #[spec(fn(NonNull<T>[@base, @addr, @size], count: usize)
        -> NonNull<T>[base, addr + count * T::size_of(), size - count * T::size_of()]
            requires addr >= base && size >= 0 && count * T::size_of() <= size)]
    unsafe fn add(self, count: usize) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L729
    #[spec(fn(NonNull<T>[@base, @addr, @size], count: usize)
        -> NonNull<T>[base, addr - count * T::size_of(), size + count * T::size_of()]
            requires addr >= base && size >= 0 && count * T::size_of() <= addr - base)]
    unsafe fn sub(self, count: usize) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L576
    #[spec(fn(NonNull<T>[@base, @addr, @size], count: isize)
        -> NonNull<T>[base, addr + count * T::size_of(), size - count * T::size_of()]
            requires addr >= base && size >= 0 && count * T::size_of() <= size && addr + count * T::size_of() >= base)]
    unsafe fn offset(self, count: isize) -> Self;
}
