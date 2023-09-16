#![feature(register_tool)]
#![register_tool(flux)]

// MutToConstPointer
pub unsafe fn test00(p: *mut i32) {
    let _ = p as *const i32;
}

// Read from a raw mut pointer
pub unsafe fn test01_mut(p: *mut i32) -> i32 {
    *p
}

// Read from a raw const pointer
pub unsafe fn test01_const(p: *const i32) -> i32 {
    *p
}

// Pointer subtyping
pub unsafe fn test02_mut_const(p: *mut i32) -> *const i32 {
    p
}

// Pointer subtyping
pub unsafe fn test02_mut_mut(p: *mut i32) -> *mut i32 {
    p
}

// Pointer subtyping
pub unsafe fn test02_const_const(p: *const i32) -> *const i32 {
    p
}

// Borrow from a pointer
pub unsafe fn test03_mut(p: *mut i32) -> &'static mut i32 {
    &mut *p
}

// `rustc` rejects the below code -- `p` is a `*const` pointer ... cannot be borrowed as mutable
// Borrow from a pointer
// unsafe fn test03_const(p: *const i32) -> &'static mut i32 {
//     unsafe { &mut *p }
// }
