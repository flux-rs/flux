use core::marker::PointeeSized;

use flux_attrs::*;

defs! {
    fn uif_eq<A, B>(a: A, b: B) -> bool;
    fn uif_ne<A, B>(a: A, b: B) -> bool;
}

#[extern_spec]
#[assoc(
    fn eq(x: Self, y: Rhs) -> bool { uif_eq(x, y) }
    fn ne(x: Self, y: Rhs) -> bool { uif_ne(x, y) }
)]
trait PartialEq<Rhs: PointeeSized = Self>: PointeeSized {
    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool[Self::eq(s, t)] )]
    fn eq(&self, other: &Rhs) -> bool;

    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool[Self::ne(s, t)] )]
    fn ne(&self, other: &Rhs) -> bool;
}
