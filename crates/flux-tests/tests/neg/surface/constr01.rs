#[flux::refined_by(a: int, b: int)]
struct Foo {
    #[flux::field({i32[@a] | 0 <= a})]
    x: i32,
    #[flux::field({i32[@b] | a <= b})]
    y: i32,
}

#[flux::sig(fn(&Foo) -> bool[true])]
fn test1(foo: &Foo) -> bool {
    foo.x < foo.y //~ ERROR refinement type
}

#[flux::sig(fn({&Foo[@a, @b] | b == 20}) -> i32[20])]
fn test2(foo: &Foo) -> i32 {
    foo.y
}

pub fn test() {
    let foo = Foo { x: 10, y: 200 };
    test1(&foo);
    test2(&foo); //~ ERROR refinement type
}
