#[flux::generics(Self as base)]
#[flux::predicate{ f : (Self) -> bool }]
trait MyTrait {
    fn method(&self) -> i32;
}

#[flux::predicate{ f : |x| { 0 < x } }]
impl MyTrait for i32 {
    fn method(&self) -> i32 {
        10
    }
}

#[flux::sig({&T[@x] | <T as MyTrait>::f(x)})]
fn bob<T: MyTrait>(x: &T) {
    x.method()
}

fn test() {
    let z0 = 0;
    bob(&z0); //~ ERROR refinement type

    let z1 = 1;
    bob(&z1);
}
