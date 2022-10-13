#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

pub struct Bob { 
    #[flux::field(RVec<i32>{n:n>0})]
    elems: RVec<i32>,
}

#[flux::sig(fn(&RVec<i32>{n:n > 0}) -> i32)]
pub fn give(vec: &RVec<i32>) -> i32 {
    vec[0]
}

#[flux::sig(fn(&Bob) -> i32)]
pub fn give2(bob: &Bob) -> i32 {
    bob.elems[0]
}

#[flux::sig(fn(n: RVec<i32>{n > 0}) -> usize{x : x < n})]
pub fn min_index(vec: RVec<i32>) -> usize {
    let sz = vec.len();
    let mut res: usize = 0;
    let mut i: usize = 0;

    while i < sz {
        res = if vec[i] < vec[res] { i } else { res };

        i = i + 1;
    }
    res
}
