#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(i32{v : v > 0}, i32{v : v > 0}) -> i32{v : v > 0})]
pub fn gcd(mut a: i32, mut b: i32) -> i32 {
    while a % b > 0 {
        let t = a % b;
        a = b;
        b = t;
    }

    b
}
