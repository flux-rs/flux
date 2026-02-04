#[flux::opts(check_raw_pointer = "checked")]
pub fn read(x: *const i32) -> i32 {
    unsafe { *x } //~ ERROR raw pointer dereference may be unsafe
}
