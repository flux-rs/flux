use flux_attrs::*;

#[extern_spec(std::convert)]
#[assume_parametric(T)] //~ ERROR `assume_parametric` is not allowed on extern spec traits
trait From<T> {
    fn from(value: T) -> Self;
}
