#[flux_rs::refined_by(n: int)]
pub struct MyStruct {
    #[flux_rs::field(i32[n])]
    n: i32,
}

impl MyStruct {
    #[flux_rs::no_panic_if(n != 0)]
    #[flux_rs::sig(fn (s: &Self[@n]) -> i32[9])]
    fn foo(&self) -> i32 {
        if self.n == 0 {
            panic!("AHH!");
        }
        9
    }
}

#[flux_rs::no_panic]
fn bar() {
    let s = MyStruct { n: 3 };
    s.foo(); // this is fine
    let s = MyStruct { n: 0 };
    s.foo(); //~ ERROR: may panic
}
