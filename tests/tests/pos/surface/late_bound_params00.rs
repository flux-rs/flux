// Refinement params of a fn are early-bound only if they appear in a where-clause or in an opaque
// type (`impl Trait`) of the signature; the rest are late-bound in the signature.

// `n` is late-bound
#[flux::spec(fn(x: i32[@n]) -> i32[n + 1])]
pub fn inc(x: i32) -> i32 {
    x + 1
}

#[flux::spec(fn(x: i32) -> i32[x + 2])]
pub fn inc_twice(x: i32) -> i32 {
    inc(inc(x))
}

// `off` is early-bound: it appears in a where-clause
#[flux::spec(fn(tagged: usize, off: usize, f: F) -> usize{v: v <= off} where F: FnOnce(usize) -> usize{v: v <= off})]
pub fn call_bounded<F: FnOnce(usize) -> usize>(tagged: usize, off: usize, f: F) -> usize {
    f(tagged)
}

#[flux::spec(fn() -> usize{v: v <= 10})]
pub fn use_call_bounded() -> usize {
    call_bounded(3, 10, |x| if x <= 10 { x } else { 10 })
}

// `n` is early-bound: it appears in an opaque type
#[flux::spec(fn(x: i32[@n]) -> impl Iterator<Item = i32{v: v == n}>)]
pub fn repeat(x: i32) -> impl Iterator<Item = i32> {
    std::iter::once(x)
}

// `a` is early-bound (where-clause), `b` is late-bound
#[flux::spec(fn(a: usize, b: usize, f: F) -> usize{v: v <= a + b} where F: FnOnce(usize) -> usize{v: v <= a})]
pub fn mixed<F: FnOnce(usize) -> usize>(a: usize, b: usize, f: F) -> usize {
    f(0) + b
}

#[flux::spec(fn() -> usize{v: v <= 11})]
pub fn use_mixed() -> usize {
    mixed(5, 6, |_| 5)
}

// Late-bound location params (`&strg`) in `ensures`
#[flux::spec(fn(x: &strg i32[@n]) ensures x: i32[n + 1])]
pub fn incr(x: &mut i32) {
    *x += 1;
}

#[flux::spec(fn() -> i32[2])]
pub fn use_incr() -> i32 {
    let mut x = 1;
    incr(&mut x);
    x
}
