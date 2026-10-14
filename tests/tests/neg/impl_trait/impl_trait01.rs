#![feature(allocator_ext, try_trait_v2)]

#[path = "../../lib/parametric_std.rs"]
mod parametric_std;

#[flux::sig(fn (x:i32) -> impl Iterator<Item = i32{v:x<=v}>)]
pub fn lib(x: i32) -> impl Iterator<Item = i32> {
    Some(x).into_iter()
}

#[flux::sig(fn (k:i32) -> Option<i32{v:k < v}>)]
pub fn test_client(k: i32) -> Option<i32> {
    let mut it = lib(k);
    it.next()
} //~ ERROR refinement type
