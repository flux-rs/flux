#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::defs {
    qualifier Sub2(x: int, a: int, b:int) { x == a - b }
}]
#[path = "../../lib/rvec.rs"]
pub mod rvec;

use rvec::RVec;

#[flux::refined_by(x: int, y:int)]
pub struct Pair {
    #[flux::field(i32[@x])]
    pub x: i32,
    #[flux::field(i32[@y])]
    pub y: i32,
}

#[flux::sig(fn(a: i32) -> RVec<Pair{v : v.x + v.y <= a }>)]
pub fn mk_pairs_with_bound(a: i32) -> RVec<Pair> {
    let mut i = 0;
    let mut res = RVec::new();
    while i < a {
        let p = Pair { x: i, y: a - i };
        res.push(p);
        i += 1;
    }
    res
}
