#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(it: I) where I: Iterator<Item = i32{v:x<=v}>)]
pub fn foo<I>(x:i32, it: I) where I: Iterator<Item = i32>,
{
    for v in it {
        assert(x <= v)
    }
}

pub fn test1() {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    foo(0, v.into_iter());
}

#[flux::sig(fn(v: Vec<i32{v:70<=v}>))]
pub fn test_ok(v: Vec<i32>) {
    let zig = v.into_iter();
    foo(55, zig);
}
