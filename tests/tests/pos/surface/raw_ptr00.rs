#[flux::opts(check_raw_pointer = "checked")]
#[flux::spec(fn (ptr: *const {v: v > 0} i32) -> i32)]
fn read(ptr: *const i32) -> i32 {
    unsafe { *ptr }
}

#[flux::opts(check_raw_pointer = "checked")]
#[flux::spec(fn (ptr: *const[10] i32) -> i32)]
fn read_ix(ptr: *const i32) -> i32 {
    unsafe { *ptr }
}

#[flux::opts(check_raw_pointer = "checked")]
#[flux::spec(fn (ptr: *mut{v: v > 0} i32, value: i32))]
fn write_i32(ptr: *mut i32, value: i32) {
    unsafe {
        *ptr = value;
    }
}

#[flux::opts(check_raw_pointer = "checked")]
#[flux::spec(fn (ptr: *mut[99] i32, value: i32))]
fn write_ix_i32(ptr: *mut i32, value: i32) {
    unsafe {
        *ptr = value;
    }
}

#[flux::opts(check_raw_pointer = "checked")]
#[flux::spec(fn (ptr: *mut{v: v > 0} T, value: T))]
fn write<T>(ptr: *mut T, value: T) {
    unsafe {
        *ptr = value;
    }
}

#[flux::opts(check_raw_pointer = "checked")]
#[flux::spec(fn (ptr: *mut[99] T, value: T))]
fn write_ix<T>(ptr: *mut T, value: T) {
    unsafe {
        *ptr = value;
    }
}
