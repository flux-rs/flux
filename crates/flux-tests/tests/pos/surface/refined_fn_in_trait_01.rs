#[flux::generics(Self as base)]
pub trait MyTrait {
    #[flux::sig(fn<refine p: Self -> bool>(&Self{v: p(v)}) -> Self{v: p(v)})]
    fn foo1(&self) -> Self;
}

#[flux::sig(fn<T as base, refine q: T -> bool> (&T{v:q(v)}) -> T{v: q(v)})]
pub fn bar1<T: MyTrait>(x: &T) -> T {
    x.foo1()
}

impl MyTrait for i32 {
    fn foo1(&self) -> Self {
        *self
    }
}

#[flux::sig(fn(bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let x = 42;
    assert(bar1(&x) == 42);
}
