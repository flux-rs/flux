use std::ops::{BitAnd, BitOr, Not, Shl, Shr};

use flux_rs_macro::{opaque, refined_by, sig, trusted};

macro_rules! bitops_wrapper_def {
    ($($name:ident, $type:ty, $bits:literal)*) => ($(
        #[opaque]
        #[refined_by(b: bitvec<$bits>)]
        pub struct $name($type);
    )*)
}

bitops_wrapper_def! {
    BV8, u8, 8
    BV16, u16, 16
    BV32, u32, 32
    BV64, u64, 64
    BV128, u128, 128
    BVi8, i8, 8
    BVi16, i16, 16
    BVi32, i32, 32
    BVi64, i64, 64
    BVi128, i128, 128
}

macro_rules! not_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl Not for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b]) -> $t[bv_not(b)])]
            fn not(self) -> $t { $name(!self.0) }
        }
    )*)
}

not_impl! { BV8, BV8 BV16, BV16 BV32, BV32 BV64, BV64 BV128, BV128 BVi8, BVi8 BVi16, BVi16 BVi32, BVi32 BVi64, BVi64 BVi128, BVi128 }

macro_rules! and_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl BitAnd for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_and(b1, b2)])]
            fn bitand(self, rhs: $t) -> $t { $name(self.0 & rhs.0) }
        }
    )*)
}

and_impl! { BV8, BV8 BV16, BV16 BV32, BV32 BV64, BV64 BV128, BV128 BVi8, BVi8 BVi16, BVi16 BVi32, BVi32 BVi64, BVi64 BVi128, BVi128 }

macro_rules! or_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl BitOr for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_or(b1, b2)])]
            fn bitor(self, rhs: $t) -> $t { $name(self.0 | rhs.0) }
        }
    )*)
}

or_impl! { BV8, BV8 BV16, BV16 BV32, BV32 BV64, BV64 BV128, BV128 BVi8, BVi8 BVi16, BVi16 BVi32, BVi32 BVi64, BVi64 BVi128, BVi128 }

macro_rules! shl_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl Shl for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_shl(b1, b2)])]
            fn shl(self, rhs: $t) -> $t { $name(self.0 << rhs.0) }
        }
    )*)
}

shl_impl! { BV8, BV8 BV16, BV16 BV32, BV32 BV64, BV64 BV128, BV128 BVi8, BVi8 BVi16, BVi16 BVi32, BVi32 BVi64, BVi64 BVi128, BVi128 }

macro_rules! shr_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl Shr for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_shl(b1, b2)])]
            fn shr(self, rhs: $t) -> $t { $name(self.0 >> rhs.0) }
        }
    )*)
}

shr_impl! { BV8, BV8 BV16, BV16 BV32, BV32 BV64, BV64 BV128, BV128 BVi8, BVi8 BVi16, BVi16 BVi32, BVi32 BVi64, BVi64 BVi128, BVi128 }
