#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty(fn() -> bool)]
pub fn toss() -> bool {
    true
}

#[lr::ty(fn(i32) -> i32 @ 0)]
pub fn test(mut k: i32) -> i32 { //~ ERROR postcondition might not hold
    while toss() && k < i32::MAX - 1 {
        k += 1;
    }
    while k > 0 {
        k -= 1;
    }
    k
}
