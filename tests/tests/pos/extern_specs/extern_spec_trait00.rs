use flux_rs::*;

#[extern_spec(std::cmp)]
#[generics(Self as base, Rhs as base)]
#[assoc(fn eq_rel(lhs: Self, rhs: Rhs) -> bool)]
trait PartialEq<Rhs> {
    #[sig(fn(&Self[@lhs], &Rhs[@rhs]) -> bool[<Self as PartialEq<Rhs>>::eq_rel(lhs, rhs)])]
    fn eq(&self, other: &Rhs) -> bool;
}

#[refined_by(n: int)]
struct MyInt(#[field(i32[n])] i32);

#[assoc(fn eq_rel(lhs: MyInt, rhs: MyInt) -> bool { lhs == rhs })]
impl PartialEq for MyInt {
    #[sig(fn(&Self[@lhs], &MyInt[@rhs]) -> bool[<MyInt as PartialEq<MyInt>>::eq_rel(lhs, rhs)])]
    fn eq(&self, other: &MyInt) -> bool {
        self.0 == other.0
    }
}

#[sig(fn(x: T, y: T) -> bool[<T as PartialEq<T>>::eq_rel(x, y)])]
fn test00<T: PartialEq>(x: T, y: T) -> bool {
    x == y
}

#[sig(fn(x: MyInt, y: MyInt) -> bool[x == y])]
fn test01(x: MyInt, y: MyInt) -> bool {
    test00(x, y)
}
