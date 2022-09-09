#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x:i32) -> i32)] //~ ERROR incompatible type
pub fn foo(x: bool) -> i32 {
    if x {
        1
    } else {
        2
    }
}

#[flux::sig(fn(x:i32) -> i32)] //~ ERROR incompatible type
pub fn bar(x: i32) -> bool {
    x > 0
}

#[flux::sig(fn(x:i32, y:i32) -> i32)] //~ ERROR mismatched args
pub fn baz(x: i32) -> i32 {
    x + 1
}
