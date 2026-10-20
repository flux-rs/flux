#![flux::opts(allow_raw_deref = "ok", std_extern_specs = "true")]

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

#[flux::spec(fn (x: {*const[@base, @addr, @size] [u32] |
    addr % 4 == 2 && addr > 0 && addr >= base && size >= 0}))]
pub fn test_create_unsized_ref_misaligned(x: *const [u32]) {
    let _r = unsafe { &*x }; //~ ERROR refinement type error
}

#[flux::spec(fn (x: {*const[@base, @addr, @size] () |
    addr == 0 && base == 0 && size == 0}))]
pub fn test_create_null_zst_ref(x: *const ()) {
    let _r = unsafe { &*x }; //~ ERROR refinement type error
}

#[flux::spec(fn (x: {*const[@base, @addr, @size] () |
    addr == 0 && base == 0 && size == 0}))]
pub fn test_read_null_zst(x: *const ()) {
    let _v: () = unsafe { *x }; //~ ERROR refinement type error
}

#[flux::spec(fn (x: {*mut[@base, @addr, @size] () |
    addr == 0 && base == 0 && size == 0}))]
pub fn test_write_null_zst(x: *mut ()) {
    unsafe { *x = () }; //~ ERROR refinement type error
}

#[flux::spec(fn (x: *mut[@xptr] *mut i32)
    requires flux_core::ptr::valid(xptr, 4) &&
        flux_core::ptr::aligned_to(xptr, 4))]
pub fn test_double_deref_invalid_inner(x: *mut *mut i32) {
    let _v: i32 = unsafe { **x }; //~ ERROR refinement type error
}

// this requires proving ownership over p
pub fn test_double_deref_unrefined_inner() {
    let mut v = 0;
    let p = &raw mut v;
    let pp: *const *mut i32 = &raw const p;
    let _r = unsafe { &mut **pp }; //~ ERROR refinement type error
}

pub struct Pair {
    pub fst: i32,
    pub snd: i32,
}

#[flux::spec(fn (p: *mut[@pp] Pair) requires pp.addr == 0)]
pub unsafe fn test_addr_of_field_of_null(p: *mut Pair) {
    let q = std::ptr::addr_of_mut!((*p).fst);
    unsafe {
        *q = 1; //~ ERROR refinement type error
    }
}

pub unsafe fn test_mut_read_mut_ptr(p: *mut i32) -> &'static mut i32 {
    &mut *p //~ ERROR refinement type error
}

pub unsafe fn test_read_mut_ptr(p: *mut i32) -> i32 {
    *p //~ ERROR refinement type error
}

pub unsafe fn test_read_const_ptr(p: *const i32) -> i32 {
    *p //~ ERROR refinement type error
}

pub fn test_get_mut(vec: &mut Vec<i32>, off: usize) -> Option<&mut i32> {
    unsafe { Some(&mut *vec.as_mut_ptr().add(off)) } //~ ERROR refinement type error
                                                     //~| ERROR refinement type error
}

struct Mickey {
    vec: Vec<i32>,
}

pub struct BytesMut {
    data: *mut Mickey,
}

fn test_field_mut_ref(bytes: BytesMut) {
    let foo = bytes.data as *mut Mickey;
    unsafe {
        let _ = &mut (*foo).vec; //~ ERROR refinement type error
    }
}
