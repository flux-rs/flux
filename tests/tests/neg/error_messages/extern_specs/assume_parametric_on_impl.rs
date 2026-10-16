use flux_attrs::*;

#[extern_spec]
#[assume_parametric(T)] //~ ERROR `assume_parametric` is not allowed on extern spec impl blocks
impl<T> [T] {
    #[spec(fn(&Self[@n]) -> Option<&T>[n != 0])]
    fn first(&self) -> Option<&T>;
}

#[assume_parametric(T)] //~ ERROR `assume_parametric` is not allowed on extern spec impl blocks
#[extern_spec]
impl<T> Option<T> {
    #[spec(fn(Option<T>[true]) -> T)]
    fn unwrap(self) -> T;
}
