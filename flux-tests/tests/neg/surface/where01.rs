#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int, b: int)]
struct Foo {
    #[flux::field(i32[@a] where 0 <= a)]
    x: i32,
    #[flux::field(i32[@b] where a < b)]
    y: i32,
}

#[flux::sig(fn(&Foo) -> bool[true])]
fn test1(foo: &Foo) -> bool {
    foo.x == foo.y    //~ ERROR postcondition
}


fn test2() {
    let foo = Foo { x: 20, y: 10 };
    test1(&foo);
    test2(&foo); //~ ERROR precondition
}
