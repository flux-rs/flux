//! An `hrn` parameter used in the refinement of an `Fn`-trait bound.
//!
//! The parameter is applied in the `where` clause, so it must be early bound.

#[flux::sig(fn [hrn p: (int, int) -> bool](n:i32, frog: F) -> i32{v:p(n, v)}
            where F: FnOnce(i32[@x]) -> i32{v:p(x, v)})]
fn lib<F>(n: i32, frog: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    frog(n)
}

#[flux::sig(fn (k: i32) -> i32[k+10])]
fn test_10(k: i32) -> i32 {
    let k_10 = lib(k, |x| x + 11);
    k_10 //~ ERROR refinement type
}
