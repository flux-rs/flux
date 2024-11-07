use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use flux_rs_macro::{opaque, refined_by, sig, trusted};

macro_rules! bitops_wrapper_def {
    ($($name:ident, $type:ty, $bits:literal)*) => ($(
        #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
        #[opaque]
        #[refined_by(b: bitvec<$bits>)]
        pub struct $name($type);
    )*)
}

bitops_wrapper_def! {
    BV32, u32, 32
    BV64, u64, 64
    BVi32, i32, 32
    BVi64, i64, 64
}

macro_rules! into_impl {
    ($($from_t:ty, $into_t:ty, $func:ident)*) => ($(
        impl Into<$into_t> for $from_t {
            #[trusted]
            #[sig(fn ($from_t[@b]) -> $into_t[$func(b)])]
            fn into(self) -> $into_t { self.0 }
        }
    )*)
}

into_impl! {
    BV32, u32, bv_bv32_to_int
    BV64, u64, bv_bv64_to_int
    BVi32, i32, bv_bv32_to_int
    BVi64, i64, bv_bv64_to_int
}

macro_rules! from_impl {
    ($($name:ident, $into_t:ty, $from_t:ty, $func:ident)*) => ($(
        impl From<$from_t> for $into_t {
            #[trusted]
            #[sig(fn ($from_t[@b]) -> $into_t[$func(b)])]
            fn from(value: $from_t) -> $into_t { $name(value) }
        }
    )*)
}

from_impl! {
    BV32, BV32, u32, bv_int_to_bv32
    BV64, BV64, u64, bv_int_to_bv64
    BVi32, BVi32, i32, bv_int_to_bv32
    BVi64, BVi64, i64, bv_int_to_bv64
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

not_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }

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

macro_rules! and_assign_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl BitAndAssign for $t {
            #[trusted]
            #[sig(fn (self: &strg $t[@b1], $t[@b2]) ensures self: $t[bv_and(b1, b2)])]
            fn bitand_assign(&mut self, rhs: $t) { *self = *self & rhs }
        }
    )*)
}

and_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
and_assign_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }

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

macro_rules! or_assign_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl BitOrAssign for $t {
            #[trusted]
            #[sig(fn (self: &strg $t[@b1], $t[@b2]) ensures self: $t[bv_or(b1, b2)])]
            fn bitor_assign(&mut self, rhs: $t) { *self = *self | rhs }
        }
    )*)
}

or_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
or_assign_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }

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

macro_rules! shl_assign_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl ShlAssign for $t {
            #[trusted]
            #[sig(fn (self: &strg $t[@b1], $t[@b2]) ensures self: $t[bv_shl(b1, b2)])]
            fn shl_assign(&mut self, rhs: $t) { *self = *self << rhs }
        }
    )*)
}

shl_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
shl_assign_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }

macro_rules! shr_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl Shr for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_lshr(b1, b2)])]
            fn shr(self, rhs: $t) -> $t { $name(self.0 >> rhs.0) }
        }
    )*)
}

macro_rules! shr_assign_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl ShrAssign for $t {
            #[trusted]
            #[sig(fn (self: &strg $t[@b1], $t[@b2]) ensures self: $t[bv_lshr(b1, b2)])]
            fn shr_assign(&mut self, rhs: $t) { *self = *self >> rhs }
        }
    )*)
}

shr_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
shr_assign_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }

macro_rules! xor_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl BitXor for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_shl(b1, b2)])]
            fn bitxor(self, rhs: $t) -> $t { $name(self.0 ^ rhs.0) }
        }
    )*)
}

macro_rules! xor_assign_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl BitXorAssign for $t {
            #[trusted]
            #[sig(fn (self: &strg $t[@b1], $t[@b2]) ensures self: $t[bv_lshr(b1, b2)])]
            fn bitxor_assign(&mut self, rhs: $t) { *self = *self ^ rhs }
        }
    )*)
}

xor_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
xor_assign_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }

macro_rules! add_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl Add for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_shl(b1, b2)])]
            fn add(self, rhs: $t) -> $t { $name(self.0 + rhs.0) }
        }
    )*)
}

macro_rules! add_assign_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl AddAssign for $t {
            #[trusted]
            #[sig(fn (self: &strg $t[@b1], $t[@b2]) ensures self: $t[bv_lshr(b1, b2)])]
            fn add_assign(&mut self, rhs: $t) { *self = *self + rhs }
        }
    )*)
}

add_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
add_assign_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }

macro_rules! sub_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl Sub for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_shl(b1, b2)])]
            fn sub(self, rhs: $t) -> $t { $name(self.0 - rhs.0) }
        }
    )*)
}

macro_rules! sub_assign_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl SubAssign for $t {
            #[trusted]
            #[sig(fn (self: &strg $t[@b1], $t[@b2]) ensures self: $t[bv_lshr(b1, b2)])]
            fn sub_assign(&mut self, rhs: $t) { *self = *self - rhs }
        }
    )*)
}

sub_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
sub_assign_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }

macro_rules! mul_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl Mul for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_shl(b1, b2)])]
            fn mul(self, rhs: $t) -> $t { $name(self.0 * rhs.0) }
        }
    )*)
}

macro_rules! mul_assign_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl MulAssign for $t {
            #[trusted]
            #[sig(fn (self: &strg $t[@b1], $t[@b2]) ensures self: $t[bv_lshr(b1, b2)])]
            fn mul_assign(&mut self, rhs: $t) { *self = *self * rhs }
        }
    )*)
}

mul_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
mul_assign_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }

macro_rules! div_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl Div for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_shl(b1, b2)])]
            fn div(self, rhs: $t) -> $t { $name(self.0 / rhs.0) }
        }
    )*)
}

macro_rules! div_assign_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl DivAssign for $t {
            #[trusted]
            #[sig(fn (self: &strg $t[@b1], $t[@b2]) ensures self: $t[bv_lshr(b1, b2)])]
            fn div_assign(&mut self, rhs: $t) { *self = *self / rhs }
        }
    )*)
}

div_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
div_assign_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }

macro_rules! rem_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl Rem for $t {
            type Output = $t;

            #[trusted]
            #[sig(fn ($t[@b1], $t[@b2]) -> $t[bv_shl(b1, b2)])]
            fn rem(self, rhs: $t) -> $t { $name(self.0 % rhs.0) }
        }
    )*)
}

macro_rules! rem_assign_impl {
    ($($name:ident, $t:ty)*) => ($(
        impl RemAssign for $t {
            #[trusted]
            #[sig(fn (self: &strg $t[@b1], $t[@b2]) ensures self: $t[bv_lshr(b1, b2)])]
            fn rem_assign(&mut self, rhs: $t) { *self = *self % rhs }
        }
    )*)
}

rem_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
rem_assign_impl! { BV32, BV32 BV64, BV64 BVi32, BVi32 BVi64, BVi64 }
