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
