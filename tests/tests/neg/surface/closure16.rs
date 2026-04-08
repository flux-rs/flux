#[flux::sig(fn(f: F) -> ()
            where F: Fn(x: i32[@n]) -> i32[n + 1] ensures old > 0)] //~ ERROR cannot find value `old` in this scope
fn bad_missing_ensures<F>(f: F)
where
    F: Fn(i32) -> i32,
{
    let _ = f;
}
