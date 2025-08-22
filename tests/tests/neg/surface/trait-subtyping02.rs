pub trait MyTrait {
    #[flux::sig(fn[hrn p: Self -> bool](&Self{v: p(v)}) -> Self{v: p(v)})]
    fn foo1(&self) -> Self;
}

impl MyTrait for u32 {
    fn foo1(&self) -> Self {
        //~^ ERROR refinement type
        *self
    }
}
