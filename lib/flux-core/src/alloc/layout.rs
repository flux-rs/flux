#![cfg_attr(flux, flux::defs(
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

// Slightly (maybe a little more than slightly) nasty macro that generates
// a check for all powers of 2 from 2^0 to 2^63. Note that this generates
// 2*2*2*2*2**..., which should just get constant folded in SMT land.
macro_rules! pow2_defs {
    ([$($pow:tt)*] $prev:tt;) => {
        defs! { fn pow2(x: int) -> bool { x == 1 $(|| x == $pow)* } }
    };
    ([$($pow:tt)*] $prev:tt; $_exp:tt $($rest:tt)*) => {
        pow2_defs!([$($pow)* (2 * $prev)] (2 * $prev); $($rest)*);
    };
}

pow2_defs!([] 1;
    1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
    32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63
);

#[extern_spec(core::alloc)]
#[opaque]
#[refined_by(size: int, align: int)]
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
