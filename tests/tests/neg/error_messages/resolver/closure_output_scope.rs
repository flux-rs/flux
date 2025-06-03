use flux_rs::attrs::*;

#[spec(fn test(f: F) where F: FnOnce() -> i32[@n])] //~ ERROR illegal binder
fn test<F: FnOnce() -> i32>(f: F)
where
    F: FnOnce() -> i32,
{
}
