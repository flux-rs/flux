#[flux::generics(Self as base)]
pub trait MyTrait {
    #[flux::sig(fn<refine p: Self -> bool>(&Self{v: p(v)}) -> Self{v: p(v)})]
    fn foo(&self) -> Self;
}

// #[flux::trusted] // UNCOMMENT TO SEE HORRIBLE ERROR MESSAGE
#[flux::sig(fn<T as base, refine q: T -> bool> (&T{v:q(v)}) -> T{v: q(v)})]
pub fn baz<T: MyTrait>(x: &T) -> T {
    x.foo()
}
