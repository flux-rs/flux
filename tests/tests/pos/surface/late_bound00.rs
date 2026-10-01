// Refinement parameters of a function are early bound if they are mentioned in a where-clause or in
// an opaque type, or if they are locations. All other parameters are late bound.

// `n` is late bound
#[flux::sig(fn(x: i32[@n]) -> i32[n + 1])]
pub fn inc(x: i32) -> i32 {
    x + 1
}

#[flux::sig(fn(x: i32) -> i32[x + 2])]
pub fn inc_twice(x: i32) -> i32 {
    inc(inc(x))
}

// `b` is early bound because it is mentioned in a where-clause and `a` is late bound. Since `b` is
// declared after `a`, its index among the early bound parameters is different from its position.
#[flux::sig(fn(x: i32[@a], f: F, y: i32[@b]) -> i32{v: v < b}
            where F: FnOnce(i32) -> i32{v: v < b})]
pub fn call_below<F: FnOnce(i32) -> i32>(x: i32, f: F, _y: i32) -> i32 {
    f(x)
}

#[flux::sig(fn() -> i32{v: v < 10})]
pub fn use_call_below() -> i32 {
    call_below(0, |_| 3, 10)
}

// `b` is early bound because it is mentioned in an opaque type and `a` is late bound. Since `b` is
// declared after `a`, its index among the early bound parameters is different from its position.
#[flux::sig(fn(x: i32[@a], y: i32[@b]) -> impl Iterator<Item = i32{v: b <= v}>)]
pub fn at_least(x: i32, y: i32) -> impl Iterator<Item = i32> {
    Some(if x < y { y } else { x }).into_iter()
}

#[flux::sig(fn() -> Option<i32{v: 5 <= v}>)]
pub fn use_at_least() -> Option<i32> {
    at_least(1, 5).next()
}

// Locations are always early bound
#[flux::sig(fn(x: &strg i32[@n]) ensures x: i32[n + 1])]
pub fn incr(x: &mut i32) {
    *x += 1;
}

#[flux::sig(fn() -> i32[2])]
pub fn use_incr() -> i32 {
    let mut x = 1;
    incr(&mut x);
    x
}

// Late bound parameters in a trait method are universally quantified when checking the
// implementation against it
pub trait AtLeast {
    #[flux::sig(fn(x: i32[@n]) -> i32{v: v >= n})]
    fn at_least(x: i32) -> i32;
}

pub struct Exact;

impl AtLeast for Exact {
    #[flux::sig(fn(x: i32[@n]) -> i32[n])]
    fn at_least(x: i32) -> i32 {
        x
    }
}
