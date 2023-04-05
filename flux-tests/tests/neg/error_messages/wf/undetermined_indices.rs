#![feature(register_tool)]
#![register_tool(flux)]

// Unused parameter
#[flux::refined_by(n: int)] //~ ERROR parameter `n` cannot be determined
struct S1 {
    x: Vec<i32>,
}

// Used but not determined
#[flux::refined_by(n: int)] //~ ERROR parameter `n` cannot be determined
struct S2 {
    #[flux::field(Vec<i32[n]>)]
    x: Vec<i32>,
}

#[flux::alias(type A[n: int] = i32{v: v > n})] //~ ERROR parameter `n` cannot be determined
type A = i32;
