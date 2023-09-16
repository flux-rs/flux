#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn(&mut RVec<i32>[@n]) -> i32)]
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

#[flux::sig(fn(&mut RVec<i32>[@len], usize{v : v < len}, usize{v : v < len}) -> i32)]
pub fn shift_down(vec: &mut RVec<i32>, start: usize, end: usize) -> i32 {
    let mut root = start;
    loop {
        let mut child = root * 2 + 1;
        if child > end {
            break;
        } else {
            if child + 1 <= end {
                let a = vec[child];
                let b = vec[child + 1];
                if a < b {
                    child += 1;
                }
            }
            let a = vec[root];
            let b = vec[child];
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
