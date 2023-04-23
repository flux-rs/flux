#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

pub struct Foo {
    #[flux::field(i32{v: 10 <= v})]
    pub val: i32,
}

#[flux::sig(fn(c:Option<bool>) -> Option<Foo>)]
pub fn test1(c: Option<bool>) -> Option<Foo> {
    let x = 6;
    let y = 10;
    c.map(|b| if b { Foo { val: x + y } } else { Foo { val: 20 } })
}

#[flux::sig(fn(vec:&RVec<i32{v: 10 <= v}>{v: 0 < v}) -> Foo)]
fn bob(vec: &RVec<i32>) -> Foo {
    Foo { val: vec[0] }
}

#[flux::sig(fn(c:Option<bool>) -> Option<Foo>)]
pub fn test2(c: Option<bool>) -> Option<Foo> {
    let vec = rvec![100, 200, 300];
    c.map(|b| if b { bob(&vec) } else { Foo { val: 20 } })
}

#[flux::trusted]
fn frob(_vec: &RVec<RVec<i32>>) -> Foo {
    todo!()
}

pub fn test3(c: Option<bool>, mut vec: RVec<RVec<i32>>) -> Option<Foo> {
    // let mut vec = rvec![rvec![100, 200, 300]];
    c.map(|b| if b { frob(&vec) } else { Foo { val: 20 } })
}
