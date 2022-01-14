#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty(fn(i32{x: 0 < x}) -> i32{x: 0 < x})]
fn fib(n: i32) -> i32 {
    let mut k = n;
    let mut i = 1;
    let mut j = 1;
    // need i > 0, and therefore j >= 0 as well
    // i > 0 and j >= 0 on entry
    while k > 2 {
        // loop_inv(a,b);
        // Loop invariant: i > 0 && j >= 0
        let tmp = i + j;
        // tmp > 0
        j = i;
        // i > 0, so j > 0 (j >= 0)
        i = tmp;
        // tmp > 0, so i > 0
        k -= 1;
        // have i > 0 and j >= 0
    }
    i
}

// Getting "unexpected token" at b:
/*
#[lr::ty(fn<n: int{0 < n}, m: int{0 <= m}>(a: i32@{n}; ref<a>, b: i32@{m}; ref<b>) -> i32; a: i32@{n+m}, b: i32@{n})]
fn loop_inv(mut a: i32, mut b: i32) -> i32 {
    let tmp = a + b;
    b = a;
    a = tmp;
    0
}
*/