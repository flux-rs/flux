#[flux::generics(Self as base)]
pub trait MyTrait {
    #[flux::sig(fn[hrn p: Self -> bool](&Self{v: p(v)}) -> Self{v: p(v)})]
    fn foo1(&self) -> Self;

    fn foo2(&self) -> Self;
}

impl MyTrait for i32 {
    // TODO: error-message when below is missing (currently: fixpoint crash!) see tests/tests/todo/trait13.rs
    #[flux::sig(fn[hrn p: Self -> bool](&Self{v: p(v)}) -> Self{v: p(v)})]
    fn foo1(&self) -> Self {
        *self
    }

    #[flux::sig(fn[hrn q: Self -> bool](&Self{v: q(v)}) -> Self{v: q(v)})]
    fn foo2(&self) -> Self {
        *self
    }
}

#[flux::sig(fn<T as base>[hrn q: T -> bool](&T{v:q(v)}) -> T{v: q(v)})]
pub fn bar1<T: MyTrait>(x: &T) -> T {
    x.foo1()
}

#[flux::sig(fn(bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let x = 42;
    assert(bar1(&x) == 42);
    assert(x.foo2() == 42);
}
