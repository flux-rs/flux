use core::marker::PointeeSized;

use flux_attrs::*;

defs! {
    use crate::num::{max, min};
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

#[extern_spec(core::cmp)]
#[refined_by(res: int)]
enum Ordering {
    #[variant(Ordering[-1])]
    Less,
    #[variant(Ordering[0])]
    Equal,
    #[variant(Ordering[1])]
    Greater
}

#[extern_spec(core::cmp)]
#[assoc(
    fn is_eq(m: Ordering, o: Ordering, res: bool) -> bool { res <=> (m.res == o.res) }
    fn is_ne(m: Ordering, o: Ordering, res: bool) -> bool { res <=> (m.res != o.res) }
)]
impl PartialEq for Ordering {
    #[spec(fn(me: &Ordering[@m], other: &Ordering[@o]) -> bool[m == o])]
    fn eq(self: &Ordering, other: &Ordering) -> bool;
}
