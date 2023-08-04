#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn () -> impl Iterator<Item = i32{v:100<=v}>)]
pub fn test_fail() -> impl Iterator<Item = i32> {
    Some(10).into_iter() //~ ERROR refinement type
}
