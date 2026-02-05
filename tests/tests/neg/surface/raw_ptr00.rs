#[flux::opts(check_raw_pointer = "checked")]
pub fn read(x: *const i32) -> i32 {
    unsafe { *x } //~ ERROR raw pointer dereference may be unsafe
}

#[flux::opts(check_raw_pointer = "checked")]
fn write<T>(ptr: *mut T, value: T) {
    unsafe {
        *ptr = value; //~ ERROR raw pointer dereference may be unsafe
    }
}

#[flux::opts(check_raw_pointer = "checked")]
fn write_i32(ptr: *mut i32, value: i32) {
    unsafe {
        *ptr = value; //~ ERROR raw pointer dereference may be unsafe
    }
}
