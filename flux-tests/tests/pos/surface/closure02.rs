#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::trusted]
fn smap<S, F, A, B>(s: S, v: Vec<A>, f: F) -> Vec<B>
where
    F: Fn(S, A) -> B,
    S: Copy,
{
    v.into_iter().map(|x| f(s, x)).collect()
}

#[flux::sig(fn(vs: Vec<i32{v:0<=v}>) -> Vec<i32{v:3<=v}>)]
pub fn test1_old(vs: Vec<i32>) -> Vec<i32> {
    let st = 3;
    smap(st, vs, |s, x| s + x)
}

#[flux::sig(fn(vs: Option<i32{v:0<=v}>) -> Option<i32{v:3<=v}>)]
pub fn test2_old(vs: Option<i32>) -> Option<i32> {
    let y = 1;
    let z = 2;
    vs.map(|x| x + y + z)


pub struct Foo {
    #[flux::field(i32{v: 10 <= v})]
    pub val: i32,
}

pub fn test1(c: Option<bool>) -> Option<Foo> {
    let x = 6;
    let y = 10;
    c.map(|b| if b { Foo { val: x + y } } else { Foo { val: 20 } })
}

#[flux::sig(fn(vec:&RVec<i32{v: 10 <= v}>{v: 0 < v}) -> Foo)]
fn bob(vec: &RVec<i32>) -> Foo {
    Foo { val: vec[0] }
}

pub fn test2(c: Option<bool>) -> Option<Foo> {
    let vec = rvec![100, 200, 300];
    c.map(|b| if b { bob(&vec) } else { Foo { val: 20 } })
}

#[flux::trusted]
fn frob(_vec: &RVec<RVec<i32>>) -> Foo {
    todo!()
}

pub fn test3(c: Option<bool>, vec: RVec<RVec<i32>>) -> Option<Foo> {
    // let mut vec = rvec![rvec![100, 200, 300]];
    c.map(|b| if b { frob(&vec) } else { Foo { val: 20 } })
}
