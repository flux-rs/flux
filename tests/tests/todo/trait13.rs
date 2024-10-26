#[flux::generics(Self as base)]
pub trait MyTrait {
    #[flux::sig(fn[hrn p: Self -> bool](&Self{v: p(v)}) -> Self{v: p(v)})]
    fn foo1(&self) -> Self;
}

impl MyTrait for i32 {
    // TODO: error-message when below is missing (currently: fixpoint crash!)
    // #[flux::sig(fn[hrn p: Self -> bool](&Self{v: p(v)}) -> Self{v: p(v)})]
    fn foo1(&self) -> Self {
        *self
    }
}
