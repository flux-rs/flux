extern crate flux_core;

#[flux::opts(check_raw_pointer = "checked")]
#[flux::spec(fn (ptr: *const{v: v > 1} i32))]
pub fn test_add_ex(ptr: *const i32) {
    unsafe {
        let _val0 = *ptr.add(0);
        let _val1 = *ptr.add(1);
        let _val2 = *ptr.add(2); //~ ERROR: raw pointer dereference
    }
}

#[flux::opts(check_raw_pointer = "checked")]
#[flux::spec(fn (ptr: *const[2] i32))]
pub fn test_add_ix(ptr: *const i32) {
    unsafe {
        let _val0 = *ptr.add(0);
        let _val1 = *ptr.add(1);
        let _val2 = *ptr.add(2); //~ ERROR: raw pointer dereference
    }
}

#[flux::opts(check_raw_pointer = "checked")]
#[flux::spec(fn (ptr: *mut{v: v > 1} i32))]
pub fn test_add_mut_ex(ptr: *mut i32) {
    unsafe {
        *ptr.add(0) = 10;
        *ptr.add(1) = 20;
        *ptr.add(2) = 30; //~ ERROR: raw pointer dereference
    }
}

#[flux::opts(check_raw_pointer = "checked")]
#[flux::spec(fn (ptr: *mut[2] i32))]
pub fn test_add_mut_ix(ptr: *mut i32) {
    unsafe {
        *ptr.add(0) = 10;
        *ptr.add(1) = 20;
        *ptr.add(2) = 30; //~ ERROR: raw pointer dereference
    }
}
