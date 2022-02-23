#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn() -> bool)]
pub fn toss() -> bool {
    true
}

#[lr::sig(fn(k: i32{v: 0 <= v}) -> i32{v:v == 0})]
pub fn test(mut k: i32) -> i32 {
    while toss() && k < i32::MAX - 1 {
        k += 1;
    }
    while k > 0 {
        k -= 1;
    }
    k
}
