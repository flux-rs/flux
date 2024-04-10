// Step 1
#[flux::generics(Self as base)]
#[flux::assoc(fn f(self: Self) -> bool )]
trait MyTrait {
    fn method(&self) -> i32;
}

// Step 2
#[flux::sig(fn({&T[@x] | <T as MyTrait>::f(x)}))]
fn bob<T: MyTrait>(x: &T) {
    x.method()
}

// Step 3
#[flux::assoc(fn f(x: int) -> bool { 0 < x } )]
impl MyTrait for i32 {
    fn method(&self) -> i32 {
        10
    }
}

// Step 4
fn test() {
    let z0 = 0;
    bob(&z0); //~ ERROR refinement type

    let z1 = 1;
    bob(&z1);
}
