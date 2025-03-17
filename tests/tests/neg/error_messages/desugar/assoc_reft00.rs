#[flux::sig(fn(&{T[@x] | <T as i32>::f(x)}, y: i32))] //~ ERROR invalid alias refinement
pub fn bob<T>(x: &T, y: i32) {}
