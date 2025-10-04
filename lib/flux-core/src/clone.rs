use flux_attrs::*;

#[extern_spec]
#[assoc(
    fn cloned(x: Self) -> Self { x }
)]
trait Clone: Sized {
    #[spec(fn(&Self[@s]) -> Self[Self::cloned(s)])]
    fn clone(&self) -> Self;
}
