#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/surface/rvec.rs"]
mod rvec;
use rvec::RVec;

#[lr::sig(fn(vec: &mut n@RVec<i32>, b:bool) -> i32[0]; vec: RVec<i32>[n] 
          where 2 <= n)]
pub fn test1(vec: &mut RVec<i32>, b: bool) -> i32 {
    let r;
    if b {
        r = vec.get_mut(0);
    } else {
        r = vec.get_mut(1);
    }
    *r = 12;
    0
}

