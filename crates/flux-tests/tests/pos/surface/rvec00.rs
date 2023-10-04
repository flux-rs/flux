#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn() -> RVec<i32>[0])]
pub fn test0() -> RVec<i32> {
    let mv = rvec![];
    mv
}

#[flux::sig(fn() -> RVec<i32>[5])]
pub fn test1() -> RVec<i32> {
    rvec![ 12; 5 ]
}

#[flux::sig(fn(n:usize) -> RVec<i32>[n])]
pub fn test2(n: usize) -> RVec<i32> {
    rvec![ 12; n ]
}

pub fn test3() -> usize {
    let v = rvec![0, 1];
    let r = v[0];
    let r = r + v[1];
    r
}
