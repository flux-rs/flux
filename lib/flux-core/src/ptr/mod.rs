#![flux::defs {
    // The provenance of the pointer is used to determine which allocation it
    // is derived from; a pointer is dereferenceable if the memory range of
    // the given size starting at the pointer is entirely contained within the
    // bounds of that allocation.
    // See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L21-L25
    fn dereferenceable(p: ptr, num_bytes: int) -> bool {
        p.addr >= p.base && num_bytes <= p.size && p.size >= 0
    }

    // Guarantees (in order of precedence):
    // - A null pointer is never valid
    // - For memory accesses of size zero, every non-null pointer is valid for reads/writes.
    // - Memory accesses of size zero are always valid
    // - A valid pointer is dereferenceable
    // See: https://doc.rust-lang.org/std/ptr/index.html#safety
    fn valid(p: ptr, num_bytes: int) -> bool {
        p.addr != 0 && dereferenceable(p, num_bytes)
    }

    // The above is only partially true: for operations that don't convert
    // pointers into references (such as read and write), zero-sized
    // reads/writes of null pointers are valid
    // See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L41-L46
    fn valid_zst(p: ptr, num_bytes: int) -> bool {
        num_bytes == 0 || valid(p, num_bytes)
    }

    // Valid raw pointers as defined above are not necessarily properly aligned
    // (where “proper” alignment is defined by the pointee type, i.e.,
    // `*const T` must be aligned to `align_of::<T>()`). However, most
    // functions require their arguments to be properly aligned,
    // and will explicitly state this requirement in their documentation.
    // Notable exceptions to this are `read_unaligned` and `write_unaligned`.
    // See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L54-L59
    fn aligned(p: ptr, alignment: int) -> bool { p.addr % alignment == 0 }
}]

#[cfg(flux)]
use flux_attrs::*;

#[cfg(flux)]
macro_rules! ptr_specs {
    ($mutable:tt) => {
        #[extern_spec(core::ptr)]
        impl<T> *$mutable T {
            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr + count * T::size_of(), p.size - count * T::size_of()] T)]
            unsafe fn add(self, count: usize) -> Self;

            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr - count * T::size_of(), p.size + count * T::size_of()] T)]
            unsafe fn sub(self, count: usize) -> Self;

            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr + count, p.size - count] T)]
            unsafe fn byte_add(self, count: usize) -> Self;

            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr - count, p.size + count] T)]
            unsafe fn byte_sub(self, count: usize) -> Self;
        }
    };
}

#[cfg(flux)]
ptr_specs!(const);

#[cfg(flux)]
ptr_specs!(mut);

#[cfg(flux)]
#[extern_spec(core::ptr)]
// - `src` must be valid for reads or `T` must be a ZST.
// - `src` must be properly aligned. Use `read_unaligned` if this is not the case.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L1591-L1596
#[spec(fn (src: *const[@p] T) -> T requires
    valid_zst(p, T::size_of()) && aligned(p, T::align_of()))]
unsafe fn read<T>(src: *const T) -> T;

#[cfg(flux)]
#[extern_spec(core::ptr)]
#[spec(fn (src: *const[@p] T) -> T requires valid_zst(p, T::size_of()))]
// - `src` must be valid for reads.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L1744-L1748
// TODO: Why are the rules for ZSTs different here?
unsafe fn read_unaligned<T>(src: *const T) -> T;

#[cfg(flux)]
#[extern_spec(core::ptr)]
// - `dst` must be valid for writes or `T` must be a ZST.
// - `dst` must be properly aligned. Use `write_unaligned` if this is not the case.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L1843-L1846
#[spec(fn (dst: *mut[@p] T, src: T) requires
    valid_zst(p, T::size_of()) && aligned(p, T::align_of()))]
unsafe fn write<T>(dst: *mut T, src: T);

#[cfg(flux)]
#[extern_spec(core::ptr)]
// - `dst` must be valid for writes or `T` must be a ZST.
// - `dst` must be properly aligned. Use `write_unaligned` if this is not the case.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L1843-L1846
#[spec(fn (dst: *mut[@p] T, src: T) requires valid_zst(p, T::size_of()))]
unsafe fn write_unaligned<T>(dst: *mut T, src: T);
