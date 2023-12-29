#[flux::generics(Self as base)]
pub trait MyTrait {
    #[flux::sig(fn<refine p: Self -> bool>(&Self{v: p(v)}) -> Self{v: p(v)})]
    fn foo1(&self) -> Self;

    fn foo2(&self) -> Self;
}

#[flux::sig(fn<T as base, refine q: T -> bool> (&T{v:q(v)}) -> T{v: q(v)})]
pub fn bar1<T: MyTrait>(x: &T) -> T {
    x.foo1()
}

// This "verifies" unsoundly due to the parametricity of `T`.
#[flux::sig(fn<T as base, refine q: T -> bool> (&T{v:q(v)}) -> T{v: q(v)})]
pub fn bar2<T: MyTrait>(x: &T) -> T {
    x.foo2() // UNSOUNDLY VERIFIED: https://github.com/flux-rs/flux/issues/588
}

// 1. reject impl of `foo1` rejected!

impl MyTrait for i32 {
    // #[flux::sig(fn<refine p: int -> bool>(&i32{v: p(v)}) -> i32{v: p(v)})]      // WORKS
    // #[flux::sig(fn<refine p: Self -> bool>(&Self{v: p(v)}) -> Self{v: p(v)})]
    fn foo1(&self) -> Self {
        12 //~ ERROR refinement type
           // *self // OK
    }

    fn foo2(&self) -> Self {
        12 // *self
    }
}

#[flux::sig(fn(bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let x = 42;
    assert(x.foo1() == 42);
}
