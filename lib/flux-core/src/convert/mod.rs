use flux_attrs::*;

#[extern_spec(core::convert)]
#[assoc(fn into_val(x: Self, into: T) -> bool { true })]
trait TryInto<T>: Sized {
    #[spec(fn(Self[@s]) -> Result<T{v: Self::into_val(s, v)}, Self::Error>)]
    fn try_into(self) -> Result<T, Self::Error>;
}
