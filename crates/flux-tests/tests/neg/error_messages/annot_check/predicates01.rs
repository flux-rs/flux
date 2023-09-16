#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn () -> impl Iterator<Item = i32{v:1+v}>)] //~ ERROR mismatched sorts
pub fn test_pass() -> impl Iterator<Item = i32> {
    Some(10).into_iter()
}
