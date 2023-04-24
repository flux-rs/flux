#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::defs {
    qualifier MyQ1(x: int, y: int, z:int) { x == y - z }
}]

// #[path = "../../lib/rvec.rs"]
// mod rvec;
// use rvec::RVec;

// #[flux::sig(fn(lo: usize, hi:usize{lo<=hi}) -> RVec<usize>[hi-lo] )]
// pub fn range(lo: usize, hi: usize) -> RVec<usize> {
//     let mut i = lo;
//     let mut res = RVec::new();
//     while i < hi {
//         // inv: res.len() = i - lo
//         res.push(i);
//         i += 1;
//     }
//     res
// }

#[flux::sig(fn(lo: usize, hi:usize{lo<=hi}) -> usize[hi-lo] )]
pub fn test_ix(lo: usize, hi: usize) -> usize {
    let mut i = lo;
    let mut res = 0;
    while i < hi {
        // inv: res = i - lo
        res += 1;
        i += 1;
    }
    res
}

#[flux::sig(fn(lo: usize, hi:usize{lo<=hi}) -> usize{v: v == hi-lo} )]
pub fn test_ex(lo: usize, hi: usize) -> usize {
    let mut i = lo;
    let mut res = 0;
    while i < hi {
        // inv: res = i - lo
        res += 1;
        i += 1;
    }
    res
}
