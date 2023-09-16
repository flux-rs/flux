#![feature(register_tool)]
#![register_tool(flux)]

struct S<'a> {
    #[flux::field(&mut i32{v : v > 0})]
    x: &'a mut i32,
}

#[flux::sig(fn(x: i32{x >= 0}))]
fn test(x: i32) {
    let mut y = x + 1;
    let mut s = S { x: &mut y };
    *s.x -= 1; //~ ERROR assignment might be unsafe
}
