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
pub fn test1(vs: Vec<i32>) -> Vec<i32> {
    let st = 3;
    smap(st, vs, |s, x| s + x)
}

#[flux::trusted]
#[flux::sig(fn(vs: Option<i32{v:0<=v}>) -> Option<i32{v:3<=v}>)]
pub fn test2(vs: Option<i32>) -> Option<i32> {
    let y = 1;
    let z = 2;
    vs.map(|x| x + y + z)
}
