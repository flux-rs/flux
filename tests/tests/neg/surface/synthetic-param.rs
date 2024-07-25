trait MyTrait {
    #[flux::sig(fn(Self) -> i32{v: v >= 0})]
    fn method(self) -> i32;
}

#[flux::sig(fn(_) -> i32{v: v > 0})]
fn test00(x: impl MyTrait) -> i32 {
    x.method()
} //~ ERROR refinement type error
