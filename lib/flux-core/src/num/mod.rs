use flux_attrs::*;

#[extern_spec(core::num)]
impl i32 {
    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L1818-L1820
    #[no_panic]
    #[spec(fn(num: i32, rhs: i32) -> i32[if num + rhs < i32::MIN { i32::MIN } else if num + rhs > i32::MAX { i32::MAX } else { num + rhs }])]
    fn saturating_add(self, rhs: i32) -> i32;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L1864-L1866
    #[no_panic]
    #[spec(fn(num: i32, rhs: i32) -> i32[if num - rhs < i32::MIN { i32::MIN } else if num - rhs > i32::MAX { i32::MAX } else { num - rhs }])]
    fn saturating_sub(self, rhs: i32) -> i32;

    /// Panics if `self == i32::MIN` (overflow when negating in debug mode).
    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/num/int_macros.rs#L3599-L3608
    #[spec(fn(num: i32{num > i32::MIN}) -> i32[if num >= 0 { num } else if num > i32::MIN { -num } else { num }])]
    fn abs(self) -> i32;
}

#[extern_spec(core::num)]
impl usize {
    /// Core impl: https://github.com/rust-lang/rust/blob/0e95a0f4c677002a5d4ac5bc59d97885e6f51f71/library/core/src/num/uint_macros.rs#L2384-L2400
    #[no_panic]
    #[spec(fn(num: usize, rhs: usize) -> usize[if num < rhs { 0 } else { num - rhs }])]
    fn saturating_sub(self, rhs: usize) -> usize;

    /// Core impl: https://github.com/rust-lang/rust/blob/0e95a0f4c677002a5d4ac5bc59d97885e6f51f71/library/core/src/num/uint_macros.rs#L2340-L2356
    #[no_panic]
    #[spec(fn(num: usize, rhs: usize) -> usize[if num + rhs > usize::MAX { usize::MAX } else { num + rhs }])]
    fn saturating_add(self, rhs: usize) -> usize;
}

#[extern_spec(core::num)]
impl u32 {
    /// Core impl: https://github.com/rust-lang/rust/blob/0e95a0f4c677002a5d4ac5bc59d97885e6f51f71/library/core/src/num/uint_macros.rs#L2384-L2400
    #[no_panic]
    #[spec(fn(num: u32, rhs: u32) -> u32[if num < rhs { 0 } else { num - rhs }])]
    fn saturating_sub(self, rhs: u32) -> u32;

    /// Core impl: https://github.com/rust-lang/rust/blob/0e95a0f4c677002a5d4ac5bc59d97885e6f51f71/library/core/src/num/uint_macros.rs#L2340-L2356
    #[no_panic]
    #[spec(fn(num: u32, rhs: u32) -> u32[if num + rhs > u32::MAX { u32::MAX } else { num + rhs }])]
    fn saturating_add(self, rhs: u32) -> u32;
}

#[extern_spec(core::num)]
impl u64 {
    /// Core impl: https://github.com/rust-lang/rust/blob/0e95a0f4c677002a5d4ac5bc59d97885e6f51f71/library/core/src/num/uint_macros.rs#L2384-L2400
    #[no_panic]
    #[spec(fn(num: u64, rhs: u64) -> u64[if num < rhs { 0 } else { num - rhs }])]
    fn saturating_sub(self, rhs: u64) -> u64;

    /// Core impl: https://github.com/rust-lang/rust/blob/0e95a0f4c677002a5d4ac5bc59d97885e6f51f71/library/core/src/num/uint_macros.rs#L2340-L2356
    #[no_panic]
    #[spec(fn(num: u64, rhs: u64) -> u64[if num + rhs > u64::MAX { u64::MAX } else { num + rhs }])]
    fn saturating_add(self, rhs: u64) -> u64;
}
