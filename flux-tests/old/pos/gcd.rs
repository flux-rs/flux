#![feature(register_tool)]
#![register_tool(flux)]

#[flux::ty(fn(i32{n: 0 < n}, i32{m: 0 < m}) -> i32{p: 0 < p})]
pub fn gcd(mut a: i32, mut b: i32) -> i32 {
    let mut x;
    while a % b > 0 {
        x = a % b;
        a = b;
        b = x;
    }

    b
}
