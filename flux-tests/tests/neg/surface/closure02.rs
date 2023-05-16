#![feature(register_tool)]
#![register_tool(flux)]

pub struct Foo {
    #[flux::field(i32{v: 10 <= v})]
    pub val: i32,
}

#[flux::sig(fn(c:Option<bool>) -> Option<Foo>)]
pub fn test1(c: Option<bool>) -> Option<Foo> {
    let x = 6;
    c.map(|b| if b { Foo { val: x } } else { Foo { val: 20 } }) //~ ERROR: precondition might not hold
}
