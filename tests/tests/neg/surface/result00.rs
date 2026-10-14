#![feature(allocator_ext, try_trait_v2)]

#[path = "../../lib/parametric_std.rs"]
mod parametric_std;

#[flux::sig(fn() -> Result<i32[0], ()>)]
fn baz() -> Result<i32, ()> {
    Ok(0)
}

#[flux::sig(fn() -> Result<i32[2], ()>)]
pub fn baz_call() -> Result<i32, ()> {
    let r = baz()?;
    Ok(r + 1) //~ ERROR refinement type
}
