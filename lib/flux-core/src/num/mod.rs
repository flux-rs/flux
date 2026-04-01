use flux_attrs::*;

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
