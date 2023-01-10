#![feature(register_tool)]
#![register_tool(flux)]

#[flux::opaque]
#[flux::refined_by(r: real)]
struct Real;

#[flux::sig(fn(r: Real, z: i32) -> i32[r + z])] //~ ERROR mismatched sorts
fn test00(r: Real, z: i32) -> i32 {
    todo!()
}

#[flux::sig(fn(r: Real, z: i32) -> i32[z + r])] //~ ERROR mismatched sorts
fn test01(r: Real, z: i32) -> i32 {
    todo!()
}
