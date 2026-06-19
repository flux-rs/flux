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
    fn valid_no_zst(p: ptr, num_bytes: int) -> bool {
        p.addr != 0 && dereferenceable(p, num_bytes)
    }

    // The above is only partially true: for operations that don't convert
    // pointers into references (such as read and write), zero-sized
    // reads/writes of null pointers are valid
    // See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L41-L46
    fn valid(p: ptr, num_bytes: int) -> bool {
        num_bytes == 0 || valid_no_zst(p, num_bytes)
    }

    // Valid raw pointers as defined above are not necessarily properly aligned
    // (where “proper” alignment is defined by the pointee type, i.e.,
    // `*const T` must be aligned to `align_of::<T>()`). However, most
    // functions require their arguments to be properly aligned,
    // and will explicitly state this requirement in their documentation.
    // Notable exceptions to this are `read_unaligned` and `write_unaligned`.
    // See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L54-L59
    fn aligned_to(p: ptr, alignment: int) -> bool { p.addr % alignment == 0 }

    // Two byte ranges of equal length starting at p and q do not overlap.
    fn nonoverlapping(p: ptr, q: ptr, num_bytes: int) -> bool {
        p.addr + num_bytes <= q.addr || q.addr + num_bytes <= p.addr
    }
}]

use flux_attrs::*;

macro_rules! ptr_specs {
    ($mutable:tt) => {
        #[extern_spec(core::ptr)]
        impl<T> *$mutable T {
            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr + count * T::size_of(), p.size - count * T::size_of()] T
                    requires count * T::size_of() <= p.size)]
            unsafe fn add(self, count: usize) -> Self;

            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr - count * T::size_of(), p.size + count * T::size_of()] T
                    requires count * T::size_of() <= p.addr - p.base)]
            unsafe fn sub(self, count: usize) -> Self;

            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr + count, p.size - count] T
                    requires count <= p.size)]
            unsafe fn byte_add(self, count: usize) -> Self;

            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr - count, p.size + count] T
                    requires count <= p.addr - p.base)]
            unsafe fn byte_sub(self, count: usize) -> Self;

            /// Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/const_ptr.rs#L22
            #[no_panic]
            #[spec(fn (me: *$mutable[@p] T) -> bool[p.addr == 0])]
            fn is_null(self) -> bool;
        }
    };
}

ptr_specs!(const);

ptr_specs!(mut);

#[extern_spec(core::ptr)]
// - `src` must be valid for reads or `T` must be a ZST.
// - `src` must be properly aligned. Use `read_unaligned` if this is not the case.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L1591-L1596
#[spec(fn (src: *const[@p] T) -> T requires
    valid(p, T::size_of()) && aligned_to(p, T::align_of()))]
unsafe fn read<T>(src: *const T) -> T;

#[extern_spec(core::ptr)]
#[spec(fn (src: *const[@p] T) -> T requires valid(p, T::size_of()))]
// - `src` must be valid for reads.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L1744-L1748
// TODO: Why are the rules for ZSTs different here?
unsafe fn read_unaligned<T>(src: *const T) -> T;

#[extern_spec(core::ptr)]
// - `dst` must be valid for writes or `T` must be a ZST.
// - `dst` must be properly aligned. Use `write_unaligned` if this is not the case.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L1843-L1846
#[spec(fn (dst: *mut[@p] T, src: T) requires
    valid(p, T::size_of()) && aligned_to(p, T::align_of()))]
unsafe fn write<T>(dst: *mut T, src: T);

#[extern_spec(core::ptr)]
// - `dst` must be valid for writes or `T` must be a ZST.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L1843-L1846
#[spec(fn (dst: *mut[@p] T, src: T) requires valid(p, T::size_of()))]
unsafe fn write_unaligned<T>(dst: *mut T, src: T);

#[extern_spec(core::ptr)]
// - `dst` must be valid for writes of `count * size_of::<T>()` bytes.
// - `dst` must be properly aligned to `align_of::<T>()`, even for zero-size writes.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L701
#[spec(fn (dst: *mut[@p] T, val: u8, count: usize) requires
    valid(p, count * T::size_of()) && aligned_to(p, T::align_of()))]
unsafe fn write_bytes<T>(dst: *mut T, val: u8, count: usize);

#[extern_spec(core::ptr)]
// - `src` must be valid for reads of `count * size_of::<T>()` bytes, or that number must be 0.
// - `dst` must be valid for writes of `count * size_of::<T>()` bytes, or that number must be 0.
// - Both `src` and `dst` must be properly aligned, even for zero-size copies.
// Overlap between `src` and `dst` is permitted (memmove semantics).
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L627
#[spec(fn (src: *const[@src_p] T, dst: *mut[@dst_p] T, count: usize) requires
    valid(src_p, count * T::size_of()) && aligned_to(src_p, T::align_of()) &&
    valid(dst_p, count * T::size_of()) && aligned_to(dst_p, T::align_of()))]
unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize);

#[extern_spec(core::ptr)]
// - `src` must be valid for reads of `count * size_of::<T>()` bytes, or that number must be 0.
// - `dst` must be valid for writes of `count * size_of::<T>()` bytes, or that number must be 0.
// - Both `src` and `dst` must be properly aligned, even for zero-size copies.
// - The byte ranges `[src, src + count * size_of::<T>())` and `[dst, dst + count * size_of::<T>())`
//   must not overlap.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L530
#[spec(fn (src: *const[@src_p] T, dst: *mut[@dst_p] T, count: usize) requires
    valid(src_p, count * T::size_of()) && aligned_to(src_p, T::align_of()) &&
    valid(dst_p, count * T::size_of()) && aligned_to(dst_p, T::align_of()) &&
    nonoverlapping(src_p, dst_p, count * T::size_of()))]
unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize);

#[extern_spec(core::ptr)]
// - Both `x` and `y` must be valid for both reads and writes of `size_of::<T>()` bytes.
// - Both `x` and `y` must be properly aligned, even if `T` has size 0.
// Overlap between `x` and `y` is permitted.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L1316
#[spec(fn (x: *mut[@xp] T, y: *mut[@yp] T) requires
    valid(xp, T::size_of()) && aligned_to(xp, T::align_of()) &&
    valid(yp, T::size_of()) && aligned_to(yp, T::align_of()))]
unsafe fn swap<T>(x: *mut T, y: *mut T);

#[extern_spec(core::ptr)]
// - Both `x` and `y` must be valid for both reads and writes of `count * size_of::<T>()` bytes.
// - Both `x` and `y` must be properly aligned, even for zero-size swaps.
// - The byte ranges `[x, x + count * size_of::<T>())` and `[y, y + count * size_of::<T>())`
//   must not overlap.
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L1380
#[spec(fn (x: *mut[@xp] T, y: *mut[@yp] T, count: usize) requires
    valid(xp, count * T::size_of()) && aligned_to(xp, T::align_of()) &&
    valid(yp, count * T::size_of()) && aligned_to(yp, T::align_of()) &&
    nonoverlapping(xp, yp, count * T::size_of()))]
unsafe fn swap_nonoverlapping<T>(x: *mut T, y: *mut T, count: usize);
