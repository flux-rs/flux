// Without `#[assume_parametric]` on the trait, the refinement on `T` is lost
use flux_attrs::*;

trait Id<T> {
    fn id<'a>(&self, x: &'a T) -> &'a T;
}

#[spec(fn(&G, &i32{v: v > 0}) -> i32{v: v > 0})]
fn test<G: Id<i32>>(g: &G, x: &i32) -> i32 {
    *g.id(x) //~ERROR refinement type error
}
