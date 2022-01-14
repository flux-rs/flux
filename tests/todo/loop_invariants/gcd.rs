#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty(fn(i32{n: 0 < n}, i32{m: 0 < m}) -> i32{p: 0 < p})]
fn gcd(mut a: i32, mut b: i32) -> i32 {
    let mut _x = 1;
    // For a % b to be safe, need b > 0, also need a > 0 since b is set to a % b in loop
    // On initial entry, a > 0 && b > 0 from the function signature
    while (a % b > 0) {
        // loop_inv(a,b);

        // Loop invariant: a > 0 && b > 0
        x = a % b;
        // a % b > 0 from loop condition, so x > 0
        a = b;
        // have b > 0, so a > 0
        b = x;
        // have x > 0, so b > 0
    }

    b
}

// Unfortunately, % in the lr::ty causes a syntax error, so not sure if this approach would work
/*
#[lr::ty(fn<n: int{0 < n}, m: int{0 < m && (n mod m) > 0}, i: int{0 < i}, j: int{0 < j}>(a: i32@n; ref<a>, b: i32@m, ref<b>) -> i32; a: i32@i, b: i32@j )]
fn loop_inv(mut a: i32, mut b: i32) -> i32 {
    let x = a % b;
    // a % b > 0 from loop condition, so x > 0
    a = b;
    // have b > 0, so a > 0
    b = x;
    // have x > 0, so b > 0
    0
}
*/
