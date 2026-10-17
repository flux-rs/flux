#![flux::opts(allow_raw_deref = "ok")]

pub struct Pair {
    pub fst: i32,
    pub snd: i32,
}

#[flux::sig(fn (p: *mut[@pp] Pair) requires pp.addr == 0)]
pub unsafe fn test_addr_of_field_of_null(p: *mut Pair) {
    let q = std::ptr::addr_of_mut!((*p).fst);
    unsafe {
        *q = 1; //~ ERROR refinement type error
    }
}
