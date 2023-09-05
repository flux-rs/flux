#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(b:bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn (x: i32, it: I) where I: Iterator<Item = i32{v: x < v}>)]
pub fn foo<I>(x: i32, it: I)
where
    I: Iterator<Item = i32>,
{
    for val in it {
        assert(x < val)
    }
}

pub fn baz() {
    foo(1, Some(2).into_iter())
}
