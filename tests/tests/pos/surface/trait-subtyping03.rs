pub trait MyTrait {
    #[flux::trusted_impl]
    fn foo1(&mut self);
}

impl MyTrait for i32 {
    #[flux::sig(fn(self: &strg i32[@n] ) ensures self: i32[n+1])]
    fn foo1(&mut self) {
        *self += 1;
    }
}

#[flux::sig(fn() -> i32[1])]
fn ok() -> i32 {
    let mut x = 0;
    x.foo1();
    x
}
