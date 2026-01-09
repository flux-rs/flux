use flux_attrs::*;

#[extern_spec(core::convert)]
#[assoc(fn into_val(x: Self) -> T)]
trait TryInto<T>: Sized
    #[spec(fn(Self[@s]) -> Result<T[Self::into_val(s)], Self::Error>)]
    fn try_into(self) -> Result<T, Self::Error>;
}
