trait MyTrait {
    fn f1(&self) -> usize;
    fn f2(&self) -> usize;
}

struct MyImpl {}

impl MyTrait for MyImpl {
    #[flux_rs::no_panic]
    fn f1(&self) -> usize {
        self.f2()
    }
    #[flux_rs::no_panic]
    fn f2(&self) -> usize {
        2
    }
}

#[flux_rs::no_panic]
fn test00(x: &MyImpl) -> usize {
    x.f1() + x.f2()
}
