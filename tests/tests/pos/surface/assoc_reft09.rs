// See <https://github.com/flux-rs/flux/issues/1510#issuecomment-3953871782>

use flux_rs::attrs::*;

#[assoc(fn assoc1() -> bool)]
trait Trait1 {
    #[spec(fn(_) requires Self::assoc1())]
    fn method1(&mut self);
}

#[assoc(fn assoc2() -> bool)]
trait Trait2<'a, T> {
    #[spec(fn(_) requires Self::assoc2())]
    fn method2(&self);
}

struct Struct<'a, T> {
    cur: &'a T,
}

#[assoc(fn assoc1() -> bool { T::assoc2() })]
impl<'a, T: Trait2<'a, T>> Trait1 for Struct<'a, T> {
    #[spec(fn(_) requires Self::assoc1())]
    fn method1(&mut self) {
        self.cur.method2();
    }
}
