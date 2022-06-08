#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(n:i32{0 < n}) -> i32{x: 1 < x})]
pub fn fib_loop(n: i32) -> i32 { //~ ERROR postcondition might not hold
    let mut k = n;
    let mut i = 1;
    let mut j = 1;
    while k > 2 {
        let tmp = i + j;
        j = i;
        i = tmp;
        k -= 1;
    }
    i
}
