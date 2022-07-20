#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(&i32[@a], {&i32[b] : b <= a}) -> i32[a-b])]
fn sub(x: &i32, y: &i32) -> i32 {
    *y - *x
}

#[flux::sig(fn() -> i32[5])]
pub fn test() -> i32 {
    let a = 20;
    let b = 25;
    sub(&a, &b) //~ ERROR precondition
}
