#![feature(register_tool)]
#![register_tool(flux)]

use std::ptr;

pub fn test0(vec: Vec<i32>) -> *const i32 {
    vec.as_ptr()
}

pub fn buffer_write(vec: &mut Vec<i32>, off: usize, value: i32) {
    unsafe {
        ptr::write(vec.as_mut_ptr().add(off), value);
    }
}

pub fn get_mut(vec: &mut Vec<i32>, off: usize) -> Option<&mut i32> {
    unsafe { Some(&mut *vec.as_mut_ptr().add(off)) }
}

pub unsafe fn copy_nonoverlapping(vec: &mut Vec<i32>, dst: usize, src: usize, len: usize) {
    unsafe {
        ptr::copy_nonoverlapping(vec.as_mut_ptr().add(src), vec.as_mut_ptr().add(dst), len);
    }
}
