#![flux::defs {
    // The memory range [addr, addr + num_bytes) is entirely contained within
    // the pointer's allocation. In our model this is: addr >= base (not before
    // the start) and num_bytes <= size (num_bytes remaining bytes fit before
    // the end). The `size >= 0` guard rules out pointers already past the end.
    // See: https://doc.rust-lang.org/std/ptr/index.html#safety
    fn dereferenceable(p: ptr, num_bytes: int) -> bool {
        p.addr >= p.base && num_bytes <= p.size && p.size >= 0
    }

    // Non-null and dereferenceable for `num_bytes` bytes. This is the strict
    // validity predicate with no ZST exception: null is never valid, even for
    // zero-sized accesses. Used as a building block for `valid` below.
    fn valid_no_zst(p: ptr, num_bytes: int) -> bool {
        p.addr != 0 && dereferenceable(p, num_bytes)
    }

    // Validity for raw-pointer operations (ptr::read, ptr::write, etc.).
    // The Rust docs note that read and write allow null pointers when the
    // total access size is zero (i.e., T is a ZST); for all other accesses
    // the pointer must be non-null and dereferenceable.
    // See: https://doc.rust-lang.org/std/ptr/index.html#safety
    fn valid(p: ptr, num_bytes: int) -> bool {
        num_bytes == 0 || valid_no_zst(p, num_bytes)
    }

    fn addr_aligned(addr: int, alignment: int) -> bool { addr % alignment == 0 }

    // The pointer's address is a multiple of `alignment`. Most read/write
    // functions require proper alignment (align_of::<T>()); the notable
    // exceptions are read_unaligned and write_unaligned.
    // See: https://doc.rust-lang.org/std/ptr/index.html#alignment
    fn aligned_to(p: ptr, alignment: int) -> bool { addr_aligned(p.addr, alignment) }

    // The byte ranges [p.addr, p.addr + num_bytes) and [q.addr, q.addr + num_bytes)
    // do not overlap.
    fn nonoverlapping(p: ptr, q: ptr, num_bytes: int) -> bool {
        p.addr + num_bytes <= q.addr || q.addr + num_bytes <= p.addr
    }

    // The pointer itself lies within its allocation: addr >= base and size >= 0.
    // One-past-the-end pointers (size == 0) satisfy this — they are valid
    // starting points for pointer arithmetic but cannot be dereferenced.
    // Required as a precondition for all pointer arithmetic methods.
    fn in_bounds(p: ptr) -> bool { dereferenceable(p, 0) }
}]
/// These specs on `core::ptr` allow flux to enforce 2 safety properties:
/// 1. Spatial safety: A pointer may only be read or written if pointer is derived from
/// a valid allocation and the entire access would fall within the bounds of that allocation.
/// 2. Per-method UB contract safety: Some methods in `core::ptr` have additional safety
/// requirements beyond spatial safety, such as alignment or non-overlapping.
/// These specs allow flux to enforce those requirements as well.
///
/// These specs do NOT prove temporal safety.
/// To prove temporal safety, Flux would need to tie the lifetimes of allocations to the pointers derived from them,
/// which is currently out of scope.
mod non_null;

use flux_attrs::*;

macro_rules! ptr_specs {
    ($mutable:tt $(, $($extra:tt)*)?) => {
        #[extern_spec(core::ptr)]
        impl<T> *$mutable T {
            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr + count * T::size_of(), p.size - count * T::size_of()] T
                    requires in_bounds(p) && count * T::size_of() <= p.size
                    ensures addr_aligned(p.addr, T::align_of()) => addr_aligned(p.addr + count * T::size_of(), T::align_of())
            )]
            unsafe fn add(self, count: usize) -> Self;

            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr - count * T::size_of(), p.size + count * T::size_of()] T
                    requires in_bounds(p) && count * T::size_of() <= p.addr - p.base
                    ensures addr_aligned(p.addr, T::align_of()) => addr_aligned(p.addr - count * T::size_of(), T::align_of())
            )]
            unsafe fn sub(self, count: usize) -> Self;

            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr + count, p.size - count] T
                    requires in_bounds(p) && count <= p.size)]
            unsafe fn byte_add(self, count: usize) -> Self;

            #[spec(fn (me: *$mutable[@p] T, count: usize)
                -> *$mutable[p.base, p.addr - count, p.size + count] T
                    requires in_bounds(p) && count <= p.addr - p.base)]
            unsafe fn byte_sub(self, count: usize) -> Self;

            /// Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/const_ptr.rs#L22
            #[no_panic]
            #[spec(fn (me: *$mutable[@p] T) -> bool[p.addr == 0])]
            fn is_null(self) -> bool;

            /// Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/const_ptr.rs#L349
            #[spec(fn (me: *$mutable[@p] T, count: isize)
                -> *$mutable[p.base, p.addr + count * T::size_of(), p.size - count * T::size_of()] T
                    requires in_bounds(p) && count * T::size_of() <= p.size && p.addr + count * T::size_of() >= p.base
                    ensures addr_aligned(p.addr, T::align_of()) => addr_aligned(p.addr + count * T::size_of(), T::align_of())
            )]
            unsafe fn offset(self, count: isize) -> Self;

            /// Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/const_ptr.rs#L471
            #[spec(fn (me: *$mutable[@p] T, count: isize)
                -> *$mutable[p.base, p.addr + count, p.size - count] T
                    requires in_bounds(p) && count <= p.size && p.addr + count >= p.base)]
            unsafe fn byte_offset(self, count: isize) -> Self;

            // - Both `self` and `origin` must be derived from a pointer to the same allocation,
            //   and the memory range between them must be in bounds of that allocation.
            //   (`p.base == op.base` captures same-allocation provenance; `addr >= base` for
            //   each captures the in-bounds requirement from below.)
            // - The distance between the pointers in bytes must be an exact multiple of
            //   `size_of::<T>()`, so that it corresponds to a whole number of elements.
            // - `T` must not be a ZST; the function panics via `assert!(0 < size_of::<T>())`.
            // See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/const_ptr.rs#L614-L628
            #[spec(fn (me: *$mutable[@p] T, origin: *const[@op] T) -> isize[(p.addr - op.addr) / T::size_of()]
                requires p.base == op.base &&
                         in_bounds(p) && in_bounds(op) &&
                         (p.addr - op.addr) % T::size_of() == 0 &&
                         T::size_of() > 0)]
            unsafe fn offset_from(self, origin: *const T) -> isize
            where T: Sized;

            // - All safety conditions of `offset_from` apply.
            // - Additionally, `self` must be greater than or equal to `origin`.
            // See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/const_ptr.rs#L770
            #[spec(fn (me: *$mutable[@p] T, origin: *const[@op] T) -> usize[(p.addr - op.addr) / T::size_of()]
                requires p.base == op.base &&
                         in_bounds(p) && in_bounds(op) &&
                         p.addr >= op.addr &&
                         (p.addr - op.addr) % T::size_of() == 0 &&
                         T::size_of() > 0)]
            unsafe fn offset_from_unsigned(self, origin: *const T) -> usize
            where T: Sized;

            /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/const_ptr.rs#L1166
            #[spec(fn (me: *$mutable[@p] T) -> T
                requires valid(p, T::size_of()) && aligned_to(p, T::align_of()))]
            unsafe fn read(self) -> T
            where T: Sized;

            $($($extra)*)?
        }
    };
}

ptr_specs!(const);

// Rustfmt likes inserting a comma in here that breaks compilation, so we disable it for this macro invocation
#[rustfmt::skip]
ptr_specs!(
    mut,
    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/mut_ptr.rs#L1413
    #[spec(fn (me: *mut[@p] T, val: T)
        requires valid(p, T::size_of()) && aligned_to(p, T::align_of()))]
    unsafe fn write(self, val: T)
    where
        T: Sized;
    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/ptr/mut_ptr.rs#L1490
    #[spec(fn (me: *mut[@p] T, src: T) -> T
        requires valid(p, T::size_of()) && aligned_to(p, T::align_of()))]
    unsafe fn replace(self, src: T) -> T
    where
        T: Sized;
);

#[extern_spec(core::ptr)]
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L828
#[no_panic]
#[spec(fn() -> *const[0, 0, 0] T)]
fn null<T>() -> *const T;

#[extern_spec(core::ptr)]
// See: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/ptr/mod.rs#L853
#[no_panic]
#[spec(fn() -> *mut[0, 0, 0] T)]
fn null_mut<T>() -> *mut T;

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
