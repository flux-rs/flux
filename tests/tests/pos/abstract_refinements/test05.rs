//! An `hrn` parameter used in the refinement of an `Fn`-trait bound.
//!
//! This requires explicit refinement params to be in scope while resolving the `where` clause,
//! since a `where` predicate lives in `generics.predicates`. See `walk_fn_sig`.

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
    let k_10 = lib(k, |x| x + 10);
    k_10
}

#[flux::sig(fn (k: i32) -> i32[k+1])]
fn test_1(k: i32) -> i32 {
    let k_1 = lib(k, |x| x + 1);
    k_1
}
