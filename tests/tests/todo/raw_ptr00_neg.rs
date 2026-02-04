#[flux::opts(check_raw_pointer = "checked")]
pub fn read(x: *const i32) -> i32 {
    unsafe { *x } //~ ERROR raw pointer dereference may be unsafe
}

// // #[flux::spec(fn (ptr: *mut{v: v > 0} T, value: T))]
// #[flux::opts(check_raw_pointer = "checked")]
// fn write(ptr: *mut i32, value: i32) {
//     unsafe {
//         *ptr = value; //~ ERROR refinement type
//     }
// }
