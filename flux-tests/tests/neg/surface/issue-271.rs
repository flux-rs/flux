#![feature(register_tool)]
#![register_tool(flux)]

pub struct S;

#[flux::sig(fn(x: u32) -> Result<{S | x < 100}, bool>)]
pub fn test01(x: u32) -> Result<S, bool> {
    if x > 100 {
        return Err(false);
    }
    Ok(S) //~ ERROR refinement type
}

#[flux::sig(fn(x: u32) -> Option<{S | x < 100}>)]
pub fn test02(x: u32) -> Option<S> {
    if x > 100 {
        return None;
    }
    Some(S) //~ ERROR refinement type
}
