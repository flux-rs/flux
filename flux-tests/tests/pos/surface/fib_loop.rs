#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(i32{v : 0 < v}) -> i32{x : 0 < x})]
pub fn fib_loop(n: i32) -> i32 {
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
