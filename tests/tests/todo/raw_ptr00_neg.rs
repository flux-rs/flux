// #[flux::spec(fn (ptr: *const {v: v > 0} i32) -> i32)]
#[flux::opts(check_raw_pointer = "checked")]
fn read(x: *const i32) -> i32 {
    unsafe { *x } //~ ERROR refinement type
}

fn read_i32(x: i32) -> i32 {
    x
}

fn read_i32_ref(x: &i32) -> i32 {
    *x
}
// // #[flux::spec(fn (ptr: *mut{v: v > 0} T, value: T))]
// #[flux::opts(check_raw_pointer = "checked")]
// fn write(ptr: *mut i32, value: i32) {
//     unsafe {
//         *ptr = value; //~ ERROR refinement type
//     }
// }
