use flux_attrs::*;

#[extern_spec]
#[assoc(
    fn cloned(old: Self, new: Self) -> bool { true }
)]
trait Clone: Sized {
    #[spec(fn(&Self[@old]) -> Self{ new: Self::cloned(old, new) })]
    fn clone(&self) -> Self;
}
