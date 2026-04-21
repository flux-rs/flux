use flux_attrs::*;

#[extern_spec(core::convert)]
#[assoc(fn into_val(x: Self, into: T) -> bool { true })]
trait TryInto<T>: Sized {
    #[spec(fn(Self[@s]) -> Result<T{v: Self::into_val(s, v)}, Self::Error>)]
    fn try_into(self) -> Result<T, Self::Error>;
}

/// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/convert/mod.rs#L687
#[extern_spec(core::convert)]
#[assoc(fn from_val(x: T, into: Self) -> bool { true })]
trait TryFrom<T>: Sized {
    #[spec(fn(T[@s]) -> Result<Self{v: <Self as TryFrom<T>>::from_val(s, v)}, Self::Error>)]
    fn try_from(value: T) -> Result<Self, Self::Error>;
}
