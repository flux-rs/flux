#![flux::defs {
    fn clamp(v: int, lo: int, hi: int) -> int { if v < lo { lo } else if v > hi { hi } else { v } }
    // NOTE: This def implements wrapping_arithmetic without relying on the modulus operator, 
    // but it assumes `v` overshoots by at most one period, i.e. v is in [2·lo, 2·hi].
    // This holds for wrapping_add/wrapping_sub when both operands are in [lo, hi],
    // but would be incorrect for operations like wrapping_mul.
    fn wrap_once(v: int, lo: int, hi: int) -> int { if v > hi { v - (hi - lo + 1) } else if v < lo { v + (hi - lo + 1) } else { v } }
    // Rust's `/` truncates toward zero, but Flux's `/` follows SMT-LIB's Euclidean `div` 
    // (floor for positive divisors, ceiling for negative)
    // They agree when both operands are non-negative, so we reduce to that case by case-splitting.
    fn sdiv(a: int, b: int) -> int {
        if a >= 0 && b > 0 { a / b }
        else if a >= 0 && b < 0 { -(a / (-b)) }
        else if a < 0 && b > 0 { -((-a) / b) }
        else { (-a) / (-b) }
    }
}]

use flux_attrs::*;

macro_rules! int_spec {
    ($T:ident) => {
        #[extern_spec(core::num)]
        impl $T {
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L1818-L1820
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[clamp(num + rhs, $T::MIN, $T::MAX)])]
            fn saturating_add(self, rhs: $T) -> $T;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L1864-L1866
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[clamp(num - rhs, $T::MIN, $T::MAX)])]
            fn saturating_sub(self, rhs: $T) -> $T;

            /// Panics if `self == T::MIN` (overflow when negating in debug mode). If in release mode, returns `T::MIN` on overflow.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L3599-L3608
            #[spec(fn(num: $T) -> $T[if num >= 0 { num } else if num > $T::MIN { -num } else { num }])]
            fn abs(self) -> $T;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L496-L499
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> Option<$T[num + rhs]>[num + rhs >= $T::MIN && num + rhs <= $T::MAX])]
            fn checked_add(self, rhs: $T) -> Option<$T>;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L646-L649
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> Option<$T[num - rhs]>[num - rhs >= $T::MIN && num - rhs <= $T::MAX])]
            fn checked_sub(self, rhs: $T) -> Option<$T>;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L82
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn count_ones(self) -> u32;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L98-L100
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn count_zeros(self) -> u32;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L115-L117
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn leading_zeros(self) -> u32;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L131-L133
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn trailing_zeros(self) -> u32;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L147-L149
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn leading_ones(self) -> u32;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L163-L165
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn trailing_ones(self) -> u32;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L793-L801
            #[no_panic]
            #[spec(fn(num: $T) -> Option<$T[-num]>[num > $T::MIN])]
            fn checked_neg(self) -> Option<$T>;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L730-L733
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> Option<$T[num * rhs]>[num * rhs >= $T::MIN && num * rhs <= $T::MAX])]
            fn checked_mul(self, rhs: $T) -> Option<$T>;

            /// Flux's `/` follows SMT-LIB's Euclidean `div` (floor for positive divisors, ceiling
            /// for negative), which differs from Rust's truncating division for negative operands.
            /// We use `sdiv` to recover truncating semantics. See: https://smt-lib.org/theories-Ints.shtml
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L780-L789
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> Option<$T[sdiv(num, rhs)]>[rhs != 0 && (num != $T::MIN || rhs != -1)])]
            fn checked_div(self, rhs: $T) -> Option<$T>;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L2010-L2012
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[wrap_once(num + rhs, $T::MIN, $T::MAX)])]
            fn wrapping_add(self, rhs: $T) -> $T;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L2060-L2062
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[wrap_once(num - rhs, $T::MIN, $T::MAX)])]
            fn wrapping_sub(self, rhs: $T) -> $T;
        }
    };
}

macro_rules! uint_spec {
    ($T:ident) => {
        #[extern_spec(core::num)]
        impl $T {
            /// Core impl: https://github.com/rust-lang/rust/blob/0e95a0f4c677002a5d4ac5bc59d97885e6f51f71/library/core/src/num/uint_macros.rs#L2384-L2400
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[clamp(num - rhs, 0, $T::MAX)])]
            fn saturating_sub(self, rhs: $T) -> $T;

            /// Core impl: https://github.com/rust-lang/rust/blob/0e95a0f4c677002a5d4ac5bc59d97885e6f51f71/library/core/src/num/uint_macros.rs#L2340-L2356
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[clamp(num + rhs, 0, $T::MAX)])]
            fn saturating_add(self, rhs: $T) -> $T;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L531-L545
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> Option<$T[num + rhs]>[num + rhs <= $T::MAX])]
            fn checked_add(self, rhs: $T) -> Option<$T>;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L698-L709
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> Option<$T[num - rhs]>[num >= rhs])]
            fn checked_sub(self, rhs: $T) -> Option<$T>;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L84-L86
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn count_ones(self) -> u32;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L106-L108
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn count_zeros(self) -> u32;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L121-L123
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn leading_zeros(self) -> u32;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L137-L139
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn trailing_zeros(self) -> u32;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L153-L155
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn leading_ones(self) -> u32;

            /// # Incomplete: result is bounded but not precisely determined by the input value.
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L169-L171
            #[no_panic]
            #[spec(fn(num: $T) -> u32{v: v <= $T::BITS})]
            fn trailing_ones(self) -> u32;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L630-L633
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> Option<$T[num * rhs]>[num * rhs <= $T::MAX])]
            fn checked_mul(self, rhs: $T) -> Option<$T>;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L720-L727
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> Option<$T[num / rhs]>[rhs > 0])]
            fn checked_div(self, rhs: $T) -> Option<$T>;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L2210-L2212
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[wrap_once(num + rhs, 0, $T::MAX)])]
            fn wrapping_add(self, rhs: $T) -> $T;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/uint_macros.rs#L2260-L2262
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[wrap_once(num - rhs, 0, $T::MAX)])]
            fn wrapping_sub(self, rhs: $T) -> $T;
        }
    };
}

int_spec!(i8);
int_spec!(i16);
int_spec!(i32);
int_spec!(i64);
int_spec!(i128);
int_spec!(isize);

uint_spec!(u8);
uint_spec!(u16);
uint_spec!(u32);
uint_spec!(u64);
uint_spec!(u128);
uint_spec!(usize);
