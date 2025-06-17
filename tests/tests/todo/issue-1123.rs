#[flux_rs::extern_spec(core::cmp)]
#[flux_rs::assoc(fn lt(this: Self, other: Self) -> bool)]
#[flux_rs::assoc(fn le(this: Self, other: Self) -> bool)]
trait PartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    fn lt(&self, other: &Rhs) -> bool;
    fn le(&self, other: &Rhs) -> bool;
}
