#![flux::opts(allow_raw_deref = "ok")]

pub struct Pair {
    pub fst: i32,
    pub snd: i32,
}

pub unsafe fn test_addr_of_field_no_use(p: *mut Pair) {
    let _q = std::ptr::addr_of_mut!((*p).fst);
}
