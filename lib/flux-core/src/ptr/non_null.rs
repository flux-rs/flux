#![flux::defs {
    // The pointer lies within its allocation: addr >= base (not before the start)
    // and size >= 0. One-past-the-end pointers (size == 0) satisfy this — they
    // are valid starting points for arithmetic but cannot be dereferenced.
    fn nn_in_bounds(base: int, addr: int, size: int) -> bool {
        addr >= base && size >= 0
    }

    // The range [addr, addr + num_bytes) fits inside the allocation.
    fn nn_dereferenceable(base: int, addr: int, size: int, num_bytes: int) -> bool {
        addr >= base && num_bytes <= size && size >= 0
    }

    // Validity for read/write. Allows null only for ZST accesses (num_bytes == 0);
    // for NonNull the addr != 0 invariant is already guaranteed by the type, so
    // this reduces to the dereferenceable check.
    fn nn_valid(base: int, addr: int, size: int, num_bytes: int) -> bool {
        num_bytes == 0 || nn_dereferenceable(base, addr, size, num_bytes)
    }

    // The address is a multiple of `alignment`.
    fn nn_aligned_to(addr: int, alignment: int) -> bool {
        addr % alignment == 0
    }
}]

use flux_attrs::*;

#[extern_spec(core::ptr)]
#[refined_by(base: int, addr: int, size: int)]
#[invariant(addr != 0)]
struct NonNull<T>;

#[extern_spec(core::ptr)]
impl<T> NonNull<T> {
    /// Need to enforce that the pointer value is non-null, because as the name suggests, this function does not check.
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
            requires nn_in_bounds(base, addr, size) && count * T::size_of() <= size)]
    unsafe fn add(self, count: usize) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L729
    #[spec(fn(NonNull<T>[@base, @addr, @size], count: usize)
        -> NonNull<T>[base, addr - count * T::size_of(), size + count * T::size_of()]
            requires nn_in_bounds(base, addr, size) && count * T::size_of() <= addr - base)]
    unsafe fn sub(self, count: usize) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L576
    #[spec(fn(NonNull<T>[@base, @addr, @size], count: isize)
        -> NonNull<T>[base, addr + count * T::size_of(), size - count * T::size_of()]
            requires nn_in_bounds(base, addr, size) && count * T::size_of() <= size && addr + count * T::size_of() >= base)]
    unsafe fn offset(self, count: isize) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L678
    #[spec(fn(NonNull<T>[@base, @addr, @size], count: usize)
        -> NonNull<T>[base, addr + count, size - count]
            requires nn_in_bounds(base, addr, size) && count <= size)]
    unsafe fn byte_add(self, count: usize) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L760
    #[spec(fn(NonNull<T>[@base, @addr, @size], count: usize)
        -> NonNull<T>[base, addr - count, size + count]
            requires nn_in_bounds(base, addr, size) && count <= addr - base)]
    unsafe fn byte_sub(self, count: usize) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L602
    #[spec(fn(NonNull<T>[@base, @addr, @size], count: isize)
        -> NonNull<T>[base, addr + count, size - count]
            requires nn_in_bounds(base, addr, size) && count <= size && addr + count >= base)]
    unsafe fn byte_offset(self, count: isize) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L858
    #[spec(fn(NonNull<T>[@sbase, @saddr, @ssize], origin: NonNull<T>[@obase, @oaddr, @osize]) -> isize[(saddr - oaddr) / T::size_of()]
        requires sbase == obase &&
                 nn_in_bounds(sbase, saddr, ssize) &&
                 nn_in_bounds(obase, oaddr, osize) &&
                 (saddr - oaddr) % T::size_of() == 0 &&
                 T::size_of() > 0)]
    unsafe fn offset_from(self, origin: NonNull<T>) -> isize
    where
        T: Sized;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L949
    #[spec(fn(NonNull<T>[@sbase, @saddr, @ssize], subtracted: NonNull<T>[@obase, @oaddr, @osize]) -> usize[(saddr - oaddr) / T::size_of()]
        requires sbase == obase &&
                 nn_in_bounds(sbase, saddr, ssize) &&
                 nn_in_bounds(obase, oaddr, osize) &&
                 saddr >= oaddr &&
                 (saddr - oaddr) % T::size_of() == 0 &&
                 T::size_of() > 0)]
    unsafe fn offset_from_unsigned(self, subtracted: NonNull<T>) -> usize
    where
        T: Sized;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L986
    #[spec(fn(NonNull<T>[@base, @addr, @size]) -> T
        requires nn_valid(base, addr, size, T::size_of()) && nn_aligned_to(addr, T::align_of()))]
    unsafe fn read(self) -> T
    where
        T: Sized;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L1141
    #[spec(fn(NonNull<T>[@base, @addr, @size], val: T)
        requires nn_valid(base, addr, size, T::size_of()) && nn_aligned_to(addr, T::align_of()))]
    unsafe fn write(self, val: T)
    where
        T: Sized;
}

#[extern_spec(core::ptr)]
impl<T> NonNull<[T]> {
    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L1420
    #[no_panic]
    #[spec(fn(data: NonNull<T>[@base, @addr, @size], len: usize) -> NonNull<[T]>[base, addr, len * T::size_of()])]
    fn slice_from_raw_parts(data: NonNull<T>, len: usize) -> Self;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/non_null.rs#L1444
    #[no_panic]
    #[spec(fn(NonNull<[T]>[@base, @addr, @size]) -> usize[size / T::size_of()]
        requires T::size_of() > 0)]
    fn len(self) -> usize;
}
