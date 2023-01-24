#![feature(register_tool)]
#![register_tool(flux)]

use std::ptr;

// #[flux::trusted]
pub fn test0(vec: Vec<i32>) -> *const i32 {
    vec.as_ptr()
}

// #[flux::trusted] // pointer
// #[flux::sig(fn (self: &mut VecDeque<T,A>[@me], off: usize{ off < me.cap }, value: T) )]
pub fn buffer_write(vec: &mut Vec<i32>, off: usize, value: i32) {
    unsafe {
        ptr::write(vec.as_mut_ptr().add(off), value);
    }
}
