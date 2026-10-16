// `#[assume_parametric]` on a trait applies to calls that resolve to its methods
use flux_attrs::*;

#[assume_parametric(T)]
trait Id<T> {
    fn id<'a>(&self, x: &'a T) -> &'a T;
}

#[spec(fn(&G, &i32{v: v > 0}) -> i32{v: v > 0})]
fn test<G: Id<i32>>(g: &G, x: &i32) -> i32 {
    *g.id(x)
}
