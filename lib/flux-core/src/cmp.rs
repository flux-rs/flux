use core::marker::PointeeSized;

use flux_attrs::*;

defs! {
    use crate::common::{max, min};
}

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

/// `Ord::min`/`Ord::max` are *provided* methods on the trait, so they live on `Ord` itself rather
/// than in `impl Ord for usize`. Without specs, `x.min(y)` returns a completely unconstrained
/// value, which loses the bound in capacity arithmetic and everything downstream of it.
///
/// The trait spec is generic in `Self`'s sort, so the actual arithmetic goes in an associated
/// refinement that only the `usize` impl defines; every other `Ord` impl keeps the vacuous default.
#[extern_spec(core::cmp)]
#[assoc(
    fn min_res(a: Self, b: Self, res: Self) -> bool { true }
    fn max_res(a: Self, b: Self, res: Self) -> bool { true }
)]
trait Ord {
    #[spec(fn(Self[@a], Self[@b]) -> Self{v: <Self as Ord>::min_res(a, b, v)})]
    fn min(self, other: Self) -> Self
    where
        Self: Sized;

    #[spec(fn(Self[@a], Self[@b]) -> Self{v: <Self as Ord>::max_res(a, b, v)})]
    fn max(self, other: Self) -> Self
    where
        Self: Sized;
}

#[extern_spec(core::cmp)]
#[assoc(
    fn min_res(a: int, b: int, res: int) -> bool { res == min(a, b) }
    fn max_res(a: int, b: int, res: int) -> bool { res == max(a, b) }
)]
impl Ord for usize {}
