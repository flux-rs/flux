use core::marker::PointeeSized;

use flux_attrs::*;

#[extern_spec]
#[assoc(
    fn is_eq(x: Self, y: Rhs, res: bool) -> bool { true }
    fn is_ne(x: Self, y: Rhs, res: bool) -> bool { true }
)]
trait PartialEq<Rhs: PointeeSized = Self>: PointeeSized {
    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool{v: Self::is_eq(s, t, v)})]
    fn eq(&self, other: &Rhs) -> bool;

    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool{v: Self::is_ne(s, t, v)})]
    fn ne(&self, other: &Rhs) -> bool;
}
