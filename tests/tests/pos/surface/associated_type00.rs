// Check we can resolve (unqualified) type projections

trait MyTrait {
    type A;
}

#[flux::sig(fn(x: T::A))]
fn foo<T: MyTrait>(x: T::A) {}
