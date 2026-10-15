// Borrow from a pointer
pub unsafe fn test03_mut(p: *mut i32) -> &'static mut i32 {
    &mut *p //~ ERROR refinement type error
}

// Read from a raw mut pointer
pub unsafe fn test01_mut(p: *mut i32) -> i32 {
    *p //~ ERROR refinement type error
}

// Read from a raw const pointer
pub unsafe fn test01_const(p: *const i32) -> i32 {
    *p //~ ERROR refinement type error
}

pub fn test_get_mut(vec: &mut Vec<i32>, off: usize) -> Option<&mut i32> {
    unsafe { Some(&mut *vec.as_mut_ptr().add(off)) } //~ ERROR refinement type error
}
