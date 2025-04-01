// test nested field projections

use flux_rs::attrs::*;

#[refined_by(x: int)]
struct S1 {
    #[field(i32[x])]
    x: i32,
}

#[refined_by(s1: S1)]
struct S2 {
    #[field(S1[s1])]
    s1: S1,
}

defs! {
    fn test(s2: S2) -> int {
        s2.s1.x
    }
}
