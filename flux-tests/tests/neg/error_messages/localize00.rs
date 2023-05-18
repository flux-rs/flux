#![feature(register_tool)]
#![register_tool(flux)]

// #[flux::sig(fn(n:i32{0 <= n}) -> i32{v: 10 <= v && (v + 20)})]
// pub fn silly(n: i32) -> i32 {
//     n + 10
// }

#[flux::sig(fn(n:i32{0 <= n}) -> i32{v: 10 <= v && v <= 20})]
pub fn post(n: i32) -> i32 {
    n + 10
}

#[flux::sig(fn(i32{v: 10 <= v && v <= 20}))]
pub fn pre(_n: i32) {}

pub fn test(n: i32) {
    if n < 15 {
        pre(n);
    }
    // let mut bob: Vec<i32> = Vec::new();
    // bob.push(true);
}

#[flux::sig(fn(n:i32, m:i32[n + 10]))]
pub fn pre2(_n: i32, _m: i32) {}

pub fn test2(n: i32) {
    pre2(n, n + n);
}

// fn baz(x: i32, y: bool) {}
