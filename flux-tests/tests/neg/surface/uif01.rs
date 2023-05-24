#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::defs {
    fn foo(x:int, y:int) -> int;
}]

#[flux::trusted]
#[flux::sig(fn(x: i32, y:i32) -> i32[foo(x, y)])]
fn foo(x: i32, y: i32) -> i32 {
    x + y
}

#[flux::sig(fn (i32[foo(10, 20)]) -> i32)]
fn bar(a: i32) -> i32 {
    return a;
}

#[flux::sig(fn())]
pub fn test() {
    let a = 10;
    let b = 30;
    let c = foo(a, b);
    bar(c); //~ ERROR refinement type
}
