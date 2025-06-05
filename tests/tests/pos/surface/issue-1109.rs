use flux_rs::attrs::*;

#[assoc(
    fn f(x: int) -> bool;
)]
trait MyTrait {}

#[refined_by(x: T)]
#[invariant(<T as MyTrait>::f(0))]
struct S<T: MyTrait> {
    #[field(T[x])]
    x: T,
}
