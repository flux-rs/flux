pub trait MyTrait {
    #[flux::sig(fn[hrn p: Self -> bool](&Self{v: p(v)}) -> Self{v: p(v)})]
    fn foo1(&self) -> Self;
}

impl MyTrait for i32 {
    #[flux::sig(fn[hrn q: Self -> bool](&Self{v: q(v)}) -> Self{v: q(v)})]
    fn foo1(&self) -> Self {
        *self
    }
}
