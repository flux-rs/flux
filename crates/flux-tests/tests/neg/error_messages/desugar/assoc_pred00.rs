#[flux::sig(fn<T as base>(&{T[@x] | <T as i32>::f(x)}, y: i32))] //~ ERROR cannot find trait `i32` in this scope
pub fn bob<T>(x: &T, y: i32) {}
