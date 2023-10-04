// Pointer subtyping
pub unsafe fn test02_const_mut(p: *const i32) -> *mut i32 {
    p as *mut i32 //~ ERROR unsupported statement
}
