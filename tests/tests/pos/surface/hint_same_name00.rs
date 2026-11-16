// Test that qualifiers and axioms with the same name declared in different modules don't
// interfere with each other when they are used in the same constraint

#[path = "../../lib/rvec.rs"]
pub mod rvec;

use flux_attrs::*;
use rvec::RVec;

#[spec(fn(bool[true]))]
fn assert(_b: bool) {}

#[refined_by(x: int, y: int)]
pub struct Pair {
    #[field(i32[x])]
    pub x: i32,
    #[field(i32[y])]
    pub y: i32,
}

mod a {
    use flux_attrs::*;

    defs! {
        fn g(x: int) -> int;

        local qualifier Q(x: int, y: int, z: int) { x + y <= z + 10 }

        local axiom GPos(x: int) { g(x) > 0 }
    }

    #[trusted]
    #[spec(fn(x: i32) -> i32[g(x)])]
    pub fn g(x: i32) -> i32 {
        x
    }
}

mod b {
    use flux_attrs::*;

    defs! {
        fn g(x: int) -> int;

        local qualifier Q(x: int, y: int, z: int) { x + y >= z - 10 }

        local axiom GPos(x: int) { g(x) > 0 }
    }

    #[trusted]
    #[spec(fn(x: i32) -> i32[g(x)])]
    pub fn g(x: i32) -> i32 {
        x
    }
}

#[axioms(a::GPos, b::GPos)]
pub fn test_axioms(x: i32) {
    assert(a::g(x) > 0 && b::g(x) > 0);
}

#[qualifiers(a::Q, b::Q)]
#[spec(fn (a: i32) -> RVec<Pair{v : v.x + v.y <= a + 10 && v.x + v.y >= a - 10}>)]
pub fn test_qualifiers(a: i32) -> RVec<Pair> {
    let mut i = 0;
    let mut res = RVec::new();
    while i < a {
        let p = Pair { x: i + 10, y: a - i };
        res.push(p);
        i += 1;
    }
    return res;
}
