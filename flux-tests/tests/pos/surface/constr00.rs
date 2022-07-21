#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]) -> ())]
fn assert(_b: bool) {}

#[flux::sig(fn(&i32[@a], { &i32[@b] : b <= a } ) -> i32[a-b])]
fn sub(x: &i32, y: &i32) -> i32 {
    let res = *x - *y;
    assert(0 <= res);
    res
}

#[flux::sig(fn() -> i32[5])]
pub fn test() -> i32 {
    let a = 20;
    let b = 15;
    sub(&a, &b)
}
