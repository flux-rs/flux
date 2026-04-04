use flux_attrs::*;

macro_rules! int_spec {
    ($T:ident) => {
        #[extern_spec(core::num)]
        impl $T {
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L1818-L1820
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[if num + rhs < $T::MIN { $T::MIN } else if num + rhs > $T::MAX { $T::MAX } else { num + rhs }])]
            fn saturating_add(self, rhs: $T) -> $T;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L1864-L1866
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[if num - rhs < $T::MIN { $T::MIN } else if num - rhs > $T::MAX { $T::MAX } else { num - rhs }])]
            fn saturating_sub(self, rhs: $T) -> $T;

            /// Panics if `self == T::MIN` (overflow when negating in debug mode).
            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L3599-L3608
            #[spec(fn(num: $T) -> $T[if num >= 0 { num } else if num > $T::MIN { -num } else { num }])]
            fn abs(self) -> $T;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L496-L499
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> Option<$T[num + rhs]>[num + rhs <= $T::MAX])]
            fn checked_add(self, rhs: $T) -> Option<$T>;

            /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L646-L649
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> Option<$T[num - rhs]>[num - rhs >= $T::MIN])]
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
        }
    };
}

macro_rules! uint_spec {
    ($T:ident) => {
        #[extern_spec(core::num)]
        impl $T {
            /// Core impl: https://github.com/rust-lang/rust/blob/0e95a0f4c677002a5d4ac5bc59d97885e6f51f71/library/core/src/num/uint_macros.rs#L2384-L2400
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[if num < rhs { 0 } else { num - rhs }])]
            fn saturating_sub(self, rhs: $T) -> $T;

            /// Core impl: https://github.com/rust-lang/rust/blob/0e95a0f4c677002a5d4ac5bc59d97885e6f51f71/library/core/src/num/uint_macros.rs#L2340-L2356
            #[no_panic]
            #[spec(fn(num: $T, rhs: $T) -> $T[if num + rhs > $T::MAX { $T::MAX } else { num + rhs }])]
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
