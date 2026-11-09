#![cfg_attr(flux, flux::defs(
    fn pow2(x: int) -> bool { x == 1 || x == 2 || x == 4 || x == 8 || x == 16 || x == 32 || x == 64 || x == 128 || x == 256 || x == 512 || x == 1024 || x == 2048 || x == 4096 || x == 8192 || x == 16384 || x == 32768 || x == 65536 || x == 131072 || x == 262144 || x == 524288 || x == 1048576 || x == 2097152 || x == 4194304 || x == 8388608 || x == 16777216 || x == 33554432 || x == 67108864 || x == 134217728 || x == 268435456 || x == 536870912 || x == 1073741824 || x == 2147483648 || x == 4294967296 || x == 8589934592 || x == 17179869184 || x == 34359738368 || x == 68719476736 || x == 137438953472 || x == 274877906944 || x == 549755813888 || x == 1099511627776 || x == 2199023255552 || x == 4398046511104 || x == 8796093022208 || x == 17592186044416 || x == 35184372088832 || x == 70368744177664 || x == 140737488355328 || x == 281474976710656 || x == 562949953421312 || x == 1125899906842624 || x == 2251799813685248 || x == 4503599627370496 || x == 9007199254740992 || x == 18014398509481984 || x == 36028797018963968 || x == 72057594037927936 || x == 144115188075855872 || x == 288230376151711744 || x == 576460752303423488 || x == 1152921504606846976 || x == 2305843009213693952 || x == 4611686018427387904 || x == 9223372036854775808 }
    fn pow2bv(x: bitvec<64>) -> bool {
        bv_and(x, bv_sub(x, bv_int_to_bv64(1))) == bv_int_to_bv64(0)
    }
    // For a layout to be valid, align must be a power of two and size must not overflow
    // isize when rounded up to the nearest multiple of align.
    //
    // The rounding formula `(size + align - 1) & !(align - 1)` is maximized when just past the
    // alignment boundary, and thus bounded by `size + align - 1`.
    // See: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/layout.rs#L80-L93
    fn is_valid_layout(s: int, a: int) -> bool {
        (s + a - 1 <= isize::MAX) && a > 0 && pow2(a)
    }

    // See: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/layout.rs#L559-L589
    fn is_valid_array_layout(n: int, size: int, align: int) -> bool {
        size == 0 || size * n + align - 1 <= isize::MAX
    }
))]

use flux_attrs::*;

#[extern_spec(core::alloc)]
#[opaque]
#[refined_by(size: int, align: int)]
#[invariant(size >= 0)]
#[invariant(align > 0 && pow2(align))]
#[invariant(size + align - 1 <= isize::MAX)]
struct Layout;

#[extern_spec(core::alloc)]
impl Layout {
    // Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/layout.rs#L206-L208
    #[no_panic]
    #[spec(fn() -> Self[T::size_of(), T::align_of()])]
    const fn new<T>() -> Self;

    // Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/layout.rs#L59-L66
    #[no_panic]
    #[spec(fn(s: usize, a: usize) -> Result<Self[s,a], _>[is_valid_layout(s, a)])]
    const fn from_size_align(size: usize, align: usize) -> Result<Layout, LayoutError>;

    // Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/layout.rs#L132-L144
    #[no_panic]
    #[spec(fn(s: usize, a: usize) -> Self[s, a] requires is_valid_layout(s, a))]
    const unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Self;

    // Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/layout.rs#L175-L177
    #[no_panic]
    #[spec(fn(&Self[@s, @a]) -> usize[s])]
    const fn size(&self) -> usize;

    // Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/layout.rs#L187-L189
    #[no_panic]
    #[spec(fn(&Self[@s, @a]) -> usize[a])]
    const fn align(&self) -> usize;

    // Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/layout.rs#L559-L589
    #[no_panic]
    #[spec(fn(n: usize) -> Result<Self[n * T::size_of(), T::align_of()],_>[
        is_valid_array_layout(n, T::size_of(), T::align_of())
    ])]
    const fn array<T>(n: usize) -> Result<Layout, LayoutError>;
}
