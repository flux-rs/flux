#![feature(register_tool)]
#![register_tool(flux)]

#[flux::trusted]
fn smap<S, F, A, B>(s: S, v: Vec<A>, f: F) -> Vec<B>
where
    F: Fn(S, A) -> B,
    S: Copy,
{
    v.into_iter().map(|x| f(s, x)).collect()
}

#[flux::sig(fn(vs: Vec<i32{v:0<=v}>) -> Vec<i32{v:3<=v}>)]
pub fn test0(vs: Vec<i32>) -> Vec<i32> {
    let st = 1;
    smap(st, vs, |s, x| s + x)
} //~ ERROR: postcondition


pub struct Foo {
    #[flux::field(i32{v: 10 <= v})]
    pub val: i32,
}

#[flux::sig(fn(c:Option<bool>) -> Option<Foo>)]
pub fn test1(c: Option<bool>) -> Option<Foo> {
    let x = 6;
    c.map(|b| if b { Foo { val: x } } else { Foo { val: 20 } }) //~ ERROR: precondition might not hold
}
