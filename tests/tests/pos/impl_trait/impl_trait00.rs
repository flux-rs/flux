#![feature(allocator_ext, try_trait_v2)]

#[path = "../../lib/parametric_std.rs"]
mod parametric_std;

pub fn test1() -> impl Iterator<Item = i32> {
    Some(10).into_iter()
}

#[flux::sig(fn () -> impl Iterator<Item = i32{v:1<=v}>)]
pub fn test2() -> impl Iterator<Item = i32> {
    Some(10).into_iter()
}

#[flux::sig(fn () -> impl Iterator<Item = i32{v:1<=v}>)]
pub fn test_lib() -> impl Iterator<Item = i32> {
    Some(10).into_iter()
}

#[flux::sig(fn () -> Option<i32{v:0<=v}>)]
pub fn test_client() -> Option<i32> {
    let mut it = test_lib();
    it.next()
}
