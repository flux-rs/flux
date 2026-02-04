// #[flux::spec(fn (ptr: *const {v: v > 0} i32) -> i32)]
// fn read(ptr: *const i32) -> i32 {
//     unsafe { *ptr } //~ ERROR refinement type
// }

// #[flux::spec(fn (ptr: *mut{v: v > 0} T, value: T))]
fn write<T>(ptr: *mut T, value: T) {
    unsafe {
        *ptr = value; // ERROR refinement type
    }
}
