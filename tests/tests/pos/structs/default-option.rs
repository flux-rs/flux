// We need this right now to not deal with the enum `Some`
#![feature(allocator_ext, try_trait_v2)]

#[path = "../../lib/parametric_std.rs"]
mod parametric_std;


#[flux::assume_parametric(T)]
#[flux::trusted]
fn some<T>(x: T) -> Option<T> {
    Option::Some(x)
}

#[flux::sig(fn() -> i32{v:10 <= v})]
pub fn test2() -> i32 {
    let opt = some(12);
    opt.unwrap()
}
