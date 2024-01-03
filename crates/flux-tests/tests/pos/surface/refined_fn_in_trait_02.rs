#[flux::generics(Self as base)]
pub trait MyTrait {
    fn foo2(&self) -> Self;
}

impl MyTrait for i32 {
    #[flux::sig(fn<refine q: Self -> bool>(&Self{v: q(v)}) -> Self{v: q(v)})]
    fn foo2(&self) -> Self {
        *self
    }
}

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

pub fn test() {
    let x = 42;
    assert(x.foo2() == 42);
}
