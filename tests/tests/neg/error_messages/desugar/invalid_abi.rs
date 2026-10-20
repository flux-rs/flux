#[flux::spec(fn(f: extern "bogus" fn(i32) -> i32) -> i32)] //~ ERROR invalid ABI
pub fn bad(f: extern "C" fn(i32) -> i32) -> i32 {
    f(0)
}
