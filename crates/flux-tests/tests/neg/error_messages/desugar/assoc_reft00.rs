#[flux::sig(fn<T as base>(&{T[@x] | <T as i32>::f(x)}, y: i32))] //~ ERROR invalid alias refinement
pub fn bob<T>(x: &T, y: i32) {}
