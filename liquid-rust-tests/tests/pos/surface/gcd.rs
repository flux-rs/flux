#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(a:i32{0 < a}, b:i32{0 < b}) -> i32{p: 0 < p})]
fn gcd(mut a: i32, mut b: i32) -> i32 {
    let mut x = 1;
    while (a % b > 0) {
        x = a % b;
        a = b;
        b = x;
    }

    b
}
