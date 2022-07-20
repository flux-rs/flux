#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int, b: int)]
struct Foo {
    #[flux::field(i32[@a] where 0 <= a)]
    x: i32,
    #[flux::field(i32[@b] where a < b)]
    y: i32,
}

fn test1(foo: &Foo) {
    assert(foo.x < foo.y)
}

#[flux::sig(fn(foo: &Foo[@a, @b] where b == 20) -> i32[20])]
fn test2(foo: &Foo) {
    let r = foo.y;
    r
}

fn test2() {
    let foo = Foo { x: 10, y: 20 };
    test1(&foo);
    test2(&foo);
}
