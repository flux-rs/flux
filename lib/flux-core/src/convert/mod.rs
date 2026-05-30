mod num;

use flux_attrs::*;

/// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/mod.rs#L612
#[extern_spec(core::convert)]
#[assoc(fn succeeds(s: Self, out: Result) -> bool { true })]
#[assoc(fn into_val(s: Self, into: T) -> bool { true })]
trait TryInto<T>: Sized {
    #[spec(fn(Self[@s]) -> Result<T{v: Self::into_val(s, v)}, Self::Error>{out: Self::succeeds(s, out)})]
    fn try_into(self) -> Result<T, Self::Error>;
}

/// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/mod.rs#L687
#[extern_spec(core::convert)]
#[assoc(fn succeeds(s: T, out: Result) -> bool { true })]
#[assoc(fn from_val(s: T, into: Self) -> bool { true })]
trait TryFrom<T>: Sized {
    #[spec(fn(T[@s]) -> Result<Self{v: Self::from_val(s, v)}, Self::Error>{out: Self::succeeds(s, out)})]
    fn try_from(value: T) -> Result<Self, Self::Error>;
}

/// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/mod.rs#L740
#[extern_spec(core::convert)]
#[assoc(fn succeeds(s: T, out: Result) -> bool { <U as TryFrom<T>>::succeeds(s, out) })]
#[assoc(fn into_val(s: T, into: U) -> bool { <U as TryFrom<T>>::from_val(s, into) })]
impl<T, U: TryFrom<T>> TryInto<U> for T {
    #[spec(fn(T[@s]) -> Result<U{v: <U as TryFrom<T>>::from_val(s, v)}, U::Error>{out: <U as TryFrom<T>>::succeeds(s, out)})]
    fn try_into(self) -> Result<U, U::Error>;
}
