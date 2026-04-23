mod num;

use flux_attrs::*;

/// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/mod.rs#L612
#[extern_spec(core::convert)]
#[assoc(fn succeeds(x: Self) -> bool { true })]
#[assoc(fn into_val(x: Self, into: T) -> bool { true })]
trait TryInto<T>: Sized {
    #[spec(fn(Self[@s]) -> Result<T{v: Self::into_val(s, v)}, Self::Error>[<Self as TryInto<T>>::succeeds(s)])]
    fn try_into(self) -> Result<T, Self::Error>;
}

/// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/mod.rs#L687
#[extern_spec(core::convert)]
#[assoc(fn succeeds(x: T) -> bool { true })]
#[assoc(fn from_val(x: T, into: Self) -> bool { true })]
trait TryFrom<T>: Sized {
    #[spec(fn(T[@x]) -> Result<Self{v: Self::from_val(x, v)}, Self::Error>[<Self as TryFrom<T>>::succeeds(x)])]
    fn try_from(value: T) -> Result<Self, Self::Error>;
}

// /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/mod.rs#L740
// #[extern_spec(core::convert)]
// impl<T, U> TryInto<U> for T
// where
//     U: TryFrom<T>,
// {
//     #[assoc(fn succeeds(x: T) -> bool { <U as TryFrom<T>>::succeeds(x) })]
//     #[assoc(fn into_val(x: T, into: U) -> bool { <U as TryFrom<T>>::from_val(x, into) })]
//     fn try_into(self) -> Result<U, U::Error>;
// }
