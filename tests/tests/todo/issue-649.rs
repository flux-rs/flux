#[flux::assoc(fn eval(x: int) -> int)]
trait MyTrait { }

impl MyTrait for i32 { } //~ ERROR missing associated refinement

#[flux::sig(fn(x: i32) -> i32[<T as MyTrait>::eval(x)])]
fn test01<T: MyTrait>(x: i32) -> i32 {
    todo!()
}

fn test02() {
    test01::<i32>(0);
}
