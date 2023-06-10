#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(n: int)]
struct S {
    #[flux::field({ i32[n] | n > 0 })]
    f1: i32,
    #[flux::field(i32{v: v > 0})]
    f2: i32,
    f3: i32,
}

// unfolding through a mutable reference should not unpack existentials but it should unpack
// constraints
fn test(x: &mut S) -> i32 {
    &mut x.f3;
    if true {}
    0
}
