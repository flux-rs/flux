#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(x: int, y:int)]
pub struct Pair {
    #[flux::field(i32[@x])]
    pub x: i32,
    #[flux::field(i32[@y])]
    pub y: i32,
}

// forall a0: int, a1: int. fn(Pair<a0, a1>) -> i32<a0 + a1>
#[flux::sig(fn (p: Pair) -> i32[p.x + p.y])]
pub fn sum_pair(p: Pair) -> i32 {
    p.x + p.y
}

// forall a0: int, a1: int. fn(Pair<a0, a1>) -> i32<a0>
#[flux::sig(fn (p: Pair) -> i32[p.x])]
pub fn fst(p: Pair) -> i32 {
    p.x
}

// forall a: int, b: int. fn(i32<a>, i32<b>) -> Pair<a, b>
#[flux::sig(fn (a: i32, b: i32) -> Pair[a,b])]
pub fn mk_pair1(a: i32, b: i32) -> Pair {
    Pair { x: a, y: b }
}

// forall a: int, b: int. fn(i32<a>, i32<b>) -> Pair{v0 v1: v0 == a && v1 == b}
#[flux::sig(fn (a: i32, b: i32) -> Pair {v : v.x == a && v.y == b})]
pub fn mk_pair2(a: i32, b: i32) -> Pair {
    Pair { x: a, y: b }
}

// forall a: int. fn(i32<a>) -> Pair{v0, v1 : v0 == a}
#[flux::sig(fn (a: i32) -> Pair{v : v.x == a})]
pub fn mk_pair_with_first(a: i32) -> Pair {
    Pair { x: a, y: 0 }
}

// forall a: int. fn(i32<a>) -> Pair{v0, v1 : v0 == a && v1 > 0}
#[flux::sig(fn (a: i32) -> Pair{v : v.x == a && v.y > 0})]
pub fn mk_pair_with_pos(a: i32) -> Pair {
    Pair { x: a, y: 10 }
}

// forall a: int. fn(i32<a>) -> Pair{v0, v1 : v0 + v1 <= a}
#[flux::sig(fn (a: i32) -> Pair{v : v.x + v.y <= a })]
pub fn mk_pair_with_bound(a: i32) -> Pair {
    Pair { x: a, y: 0 }
}
