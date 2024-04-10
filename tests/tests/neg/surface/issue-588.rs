pub trait MyTrait {
    fn foo(&self) -> Self;
}

#[flux::sig(fn<T as base, refine q: T -> bool> (&T{v:q(v)}) -> T{v: q(v)})]
pub fn bar<T: MyTrait>(x: &T) -> T {
    x.foo() //~ ERROR refinement type
}
