#![feature(register_tool)]
#![register_tool(flux)]

// ------ Test 1 -------------------------------------------------

#[flux::sig(fn(i32{v: 10 <= v && v <= 20}))]
pub fn pre(_n: i32) {}

pub fn test(n: i32) {
    if n < 15 {
        pre(n);
    }
}
// ------ Test 2 -------------------------------------------------

#[flux::sig(fn(n:i32{0 <= n}) -> i32{v: 100 <= v && v <= 200})]
pub fn post(n: i32) -> i32 {
    n + 100
}

#[flux::sig(fn(n:i32, m:i32[n + 10]))]
pub fn pre2(_n: i32, _m: i32) {}

pub fn test2(n: i32) {
    pre2(n, n + n);
}
