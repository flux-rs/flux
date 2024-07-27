#[flux::assoc(fn eval(x: int) -> int)]
trait MyTrait {}

struct Foo;

#[flux::assoc(fn eval(x: int) -> int { x + 1 })]
impl MyTrait for Foo {}

struct Bar;

impl MyTrait for Bar {} //~ ERROR associated refinement `eval` is not a member of trait `MyTrait`
                        //~^ ERROR undefined associated refinement `eval`

#[flux::sig(fn(x: i32) -> i32[<T as MyTrait>::eval(x)])]
fn test01<T: MyTrait>(x: i32) -> i32 {
    x + 2 //~ ERROR refinement type
}

#[flux::sig(fn() -> i32[1])]
pub fn test_foo() -> i32 {
    test01::<Foo>(0)
}

#[flux::sig(fn() -> i32[1])]
pub fn test_bar() -> i32 {
    test01::<Bar>(0)
}
