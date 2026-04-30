// Core impls: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/num.rs

use core::num::TryFromIntError;

use flux_attrs::*;

// no possible bounds violation — always Ok
macro_rules! try_from_unbounded {
    ($Src:ident => $($Dst:ident),+) => {$(
        #[extern_spec(core::convert)]
        #[assoc(fn succeeds(x: int, out: Result) -> bool { true })]
        #[assoc(fn from_val(x: int, into: int) -> bool { x == into })]
        impl TryFrom<$Src> for $Dst {
            #[no_panic]
            /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/num.rs#L252
            #[spec(fn($Src[@x]) -> Result<$Dst[x], _>[true])]
            fn try_from(value: $Src) -> Result<$Dst, TryFromIntError>;
        }
    )+}
}

// only negative bound — signed source, unsigned dest of same or wider width
macro_rules! try_from_lower_bounded {
    ($Src:ident => $($Dst:ident),+) => {$(
        #[extern_spec(core::convert)]
        #[assoc(fn succeeds(x: int, out: Result) -> bool { out.is_ok == (x >= 0) })]
        #[assoc(fn from_val(x: int, into: int) -> bool { x == into })]
        impl TryFrom<$Src> for $Dst {
            #[no_panic]
            /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/num.rs#L271
            #[spec(fn($Src[@x]) -> Result<$Dst[x], _>[x >= 0])]
            fn try_from(value: $Src) -> Result<$Dst, TryFromIntError>;
        }
    )+}
}

// only upper bound — unsigned source
macro_rules! try_from_upper_bounded {
    ($Src:ident => $($Dst:ident),+) => {$(
        #[extern_spec(core::convert)]
        #[assoc(fn succeeds(x: int, out: Result) -> bool { out.is_ok == (x <= $Dst::MAX) })]
        #[assoc(fn from_val(x: int, into: int) -> bool { x == into })]
        impl TryFrom<$Src> for $Dst {
            #[no_panic]
            /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/num.rs#L294
            #[spec(fn($Src[@x]) -> Result<$Dst[x], _>[x <= $Dst::MAX])]
            fn try_from(value: $Src) -> Result<$Dst, TryFromIntError>;
        }
    )+}
}

// both bounds — signed source, narrower dest
macro_rules! try_from_both_bounded {
    ($Src:ident => $($Dst:ident),+) => {$(
        #[extern_spec(core::convert)]
        #[assoc(fn succeeds(x: int, out: Result) -> bool { out.is_ok == ($Dst::MIN <= x && x <= $Dst::MAX) })]
        #[assoc(fn from_val(x: int, into: int) -> bool { x == into })]
        impl TryFrom<$Src> for $Dst {
            #[no_panic]
            /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/num.rs#L317
            #[spec(fn($Src[@x]) -> Result<$Dst[x], _>[$Dst::MIN <= x && x <= $Dst::MAX])]
            fn try_from(value: $Src) -> Result<$Dst, TryFromIntError>;
        }
    )+}
}

macro_rules! rev {
    ($mac:ident, $Src:ident => $($Dst:ident),+) => {$(
        $mac!($Dst => $Src);
    )+}
}

// unsigned integer -> unsigned integer
try_from_upper_bounded!(u16 => u8);
try_from_upper_bounded!(u32 => u8, u16);
try_from_upper_bounded!(u64 => u8, u16, u32);
try_from_upper_bounded!(u128 => u8, u16, u32, u64);

// signed integer -> signed integer
try_from_both_bounded!(i16 => i8);
try_from_both_bounded!(i32 => i8, i16);
try_from_both_bounded!(i64 => i8, i16, i32);
try_from_both_bounded!(i128 => i8, i16, i32, i64);

// unsigned integer -> signed integer
try_from_upper_bounded!(u8 => i8);
try_from_upper_bounded!(u16 => i8, i16);
try_from_upper_bounded!(u32 => i8, i16, i32);
try_from_upper_bounded!(u64 => i8, i16, i32, i64);
try_from_upper_bounded!(u128 => i8, i16, i32, i64, i128);

// signed integer -> unsigned integer
try_from_lower_bounded!(i8 => u8, u16, u32, u64, u128);
try_from_both_bounded!(i16 => u8);
try_from_lower_bounded!(i16 => u16, u32, u64, u128);
try_from_both_bounded!(i32 => u8, u16);
try_from_lower_bounded!(i32 => u32, u64, u128);
try_from_both_bounded!(i64 => u8, u16, u32);
try_from_lower_bounded!(i64 => u64, u128);
try_from_both_bounded!(i128 => u8, u16, u32, u64);
try_from_lower_bounded!(i128 => u128);

// usize/isize <-> each other
try_from_upper_bounded!(usize => isize);
try_from_lower_bounded!(isize => usize);

#[cfg(target_pointer_width = "16")]
mod ptr_try_from_impls {
    use core::num::TryFromIntError;

    use flux_attrs::*;

    try_from_upper_bounded!(usize => u8);
    try_from_unbounded!(usize => u16, u32, u64, u128);
    try_from_upper_bounded!(usize => i8, i16);
    try_from_unbounded!(usize => i32, i64, i128);

    try_from_both_bounded!(isize => u8);
    try_from_lower_bounded!(isize => u16, u32, u64, u128);
    try_from_both_bounded!(isize => i8);
    try_from_unbounded!(isize => i16, i32, i64, i128);

    rev!(try_from_upper_bounded, usize => u32, u64, u128);
    rev!(try_from_lower_bounded, usize => i8, i16);
    rev!(try_from_both_bounded, usize => i32, i64, i128);

    rev!(try_from_upper_bounded, isize => u16, u32, u64, u128);
    rev!(try_from_both_bounded, isize => i32, i64, i128);
}

#[cfg(target_pointer_width = "32")]
mod ptr_try_from_impls {
    use core::num::TryFromIntError;

    use flux_attrs::*;

    try_from_upper_bounded!(usize => u8, u16);
    try_from_unbounded!(usize => u32, u64, u128);
    try_from_upper_bounded!(usize => i8, i16, i32);
    try_from_unbounded!(usize => i64, i128);

    try_from_both_bounded!(isize => u8, u16);
    try_from_lower_bounded!(isize => u32, u64, u128);
    try_from_both_bounded!(isize => i8, i16);
    try_from_unbounded!(isize => i32, i64, i128);

    rev!(try_from_unbounded, usize => u32);
    rev!(try_from_upper_bounded, usize => u64, u128);
    rev!(try_from_lower_bounded, usize => i8, i16, i32);
    rev!(try_from_both_bounded, usize => i64, i128);

    rev!(try_from_unbounded, isize => u16);
    rev!(try_from_upper_bounded, isize => u32, u64, u128);
    rev!(try_from_unbounded, isize => i32);
    rev!(try_from_both_bounded, isize => i64, i128);
}

#[cfg(target_pointer_width = "64")]
mod ptr_try_from_impls {
    use core::num::TryFromIntError;

    use flux_attrs::*;

    try_from_upper_bounded!(usize => u8, u16, u32);
    try_from_unbounded!(usize => u64, u128);
    try_from_upper_bounded!(usize => i8, i16, i32, i64);
    try_from_unbounded!(usize => i128);

    try_from_both_bounded!(isize => u8, u16, u32);
    try_from_lower_bounded!(isize => u64, u128);
    try_from_both_bounded!(isize => i8, i16, i32);
    try_from_unbounded!(isize => i64, i128);

    rev!(try_from_unbounded, usize => u32, u64);
    rev!(try_from_upper_bounded, usize => u128);
    rev!(try_from_lower_bounded, usize => i8, i16, i32, i64);
    rev!(try_from_both_bounded, usize => i128);

    rev!(try_from_unbounded, isize => u16, u32);
    rev!(try_from_upper_bounded, isize => u64, u128);
    rev!(try_from_unbounded, isize => i32, i64);
    rev!(try_from_both_bounded, isize => i128);
}
