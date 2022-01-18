#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty(fn(usize{n: 0 < n}, usize{m: 0 < m}) -> usize{p: 0 < p})]
fn gcd(mut a: usize, mut b: usize) -> usize {
    // For a % b to be safe, need b > 0, also need a > 0 since b is set to a % b in loop
    // On initial entry, a > 0 && b > 0 from the function signature
    while a % b > 0 {
        // Loop invariant: a > 0 && b > 0
        let x = a % b;
        // a % b > 0 from loop condition, so x > 0
        a = b;
        // have b > 0, so a > 0
        b = x;
        // have x > 0, so b > 0
    }

    b
}

#[lr::ty(fn(usize{x: 0 < x}, usize{x: 0 < x}) -> usize)]
fn gcd_recursive(a: usize, b: usize) -> usize {
    if a % b > 0 {
        gcd_recursive(b, a % b)
    } else {
        b
    }
}