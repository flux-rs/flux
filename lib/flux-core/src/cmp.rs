use core::marker::PointeeSized;

use flux_attrs::*;

defs! {
    fn uif_equality<A, B>(a: A, b: B) -> bool;
}

#[extern_spec]
#[assoc(
    fn eq(x: Self, y: Rhs) -> bool;
)]
trait PartialEq<Rhs: PointeeSized = Self>: PointeeSized {
    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool[Self::eq(s, t)] )]
    fn eq(&self, other: &Rhs) -> bool;

    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool[!Self::eq(s, t)] )]
    fn ne(&self, other: &Rhs) -> bool;
}
