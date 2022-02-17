#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[lr::ty(fn<len: int>(vec: RVec<i32>@len; ref<vec>) -> i32; vec:RVec<i32>@len)]
pub fn heap_sort(vec: &mut RVec<i32>) -> i32 {
    let len = vec.len();

    if len <= 0 {
        return 0;
    }

    let mut start = len / 2;
    while start > 0 {
        start -= 1;
        shift_down(vec, start, len - 1);
    }

    let mut end = len;
    while end > 1 {
        end -= 1;
        vec.swap(0, end);
        shift_down(vec, 0, end - 1);
    }
    0
}

#[lr::ty(fn<len: int>(vec: RVec<i32>@len; ref<vec>, usize{v: 0 <= v && v < len}, usize{v: 0 <= v && v < len}) -> i32; vec: RVec<i32>@len)]
pub fn shift_down(vec: &mut RVec<i32>, start: usize, end: usize) -> i32 {
    let mut root = start;
    loop {
        let mut child = root * 2 + 1;
        if child > end {
            break;
        } else {
            if child + 1 <= end {
                let a = *vec.get(child);
                let b = *vec.get(child + 1);
                if a < b {
                    child += 1;
                }
            }
            let a = *vec.get(root);
            let b = *vec.get(child);
            if a < b {
                vec.swap(root, child);
                root = child;
            } else {
                break;
            }
        }
    }
    0
}
