#![allow(unused)]

#[flux::sig(fn(p: (i32, i32)) -> i32[p.0])]
fn fst(p: (i32, i32)) -> i32 {
    p.0
}

#[flux::sig(fn(p: (i32, i32)[@x]) -> i32[x.1])]
fn snd(p: (i32, i32)) -> i32 {
    p.1
}

#[flux::sig(fn() -> (i32, i32){v: v.1 >= v.2})]
fn mk_tuple() -> (i32, i32) {
    (0, 1)
}

#[flux::sig(fn(p: (i32{v: v > 0}, i32{v: v > 0}){v: v.0 == v.1}))]
fn test00(p: (i32, i32)) {}

fn test01() {
    test00((1, 1));
}
