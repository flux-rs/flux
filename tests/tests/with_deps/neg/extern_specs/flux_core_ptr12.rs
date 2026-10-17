#![flux::opts(allow_raw_deref = "ok")]

extern crate flux_core;

#[flux::refined_by(p: ptr)]
pub struct Holder {
    #[flux::field(*mut[p] i32)]
    pub ptr: *mut i32,
}

#[flux::spec(fn (h: Holder[@hp]))]
pub fn test_borrow_through_projection(h: Holder) {
    let _r = unsafe { &mut (*h.ptr) }; //~ ERROR refinement type error
}

#[flux::spec(fn (h: Holder[@hp], v: i32))]
pub fn test_write_through_projection(h: Holder, v: i32) {
    unsafe {
        (*h.ptr) = v; //~ ERROR refinement type error
    }
}

#[flux::spec(fn (h: Holder[@hp]))]
pub fn test_write_through_copied_ptr(h: Holder) {
    let xcopy: *mut i32 = std::ptr::addr_of_mut!(*h.ptr);
    unsafe { xcopy.write(4) } //~ ERROR refinement type error
    //~| ERROR refinement type error
}

#[flux::spec(fn (x: *mut[@xptr] i32) requires (xptr.addr % 4) != 0)]
pub fn test_create_ref_misaligned(x: *mut i32) {
    let _r = unsafe { &*x }; //~ ERROR refinement type error
}

#[flux::spec(fn (x: *mut[@xptr] T) requires (xptr.addr % T::align_of()) != 0)]
pub fn test_create_ref_misaligned_generic<T>(x: *mut T) {
    let _xref: &T = unsafe { &*x }; //~ ERROR refinement type error
}

#[flux::spec(fn (x: *mut[@xptr] *mut i32)
    requires flux_core::ptr::valid(xptr, 4) && flux_core::ptr::aligned_to(xptr, 4))]
pub fn test_double_deref_invalid_inner(x: *mut *mut i32) {
    let _v: i32 = unsafe { **x }; //~ ERROR refinement type error
}
