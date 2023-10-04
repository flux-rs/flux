#[flux::sig(fn() -> i32[0])]
pub fn float_to_int() -> i32 {
    0.0f32 as i32 //~ ERROR refinement type
}

#[flux::sig(fn() -> u32[1])]
pub fn float_to_uint() -> u32 {
    1.0f64 as u32 //~ ERROR refinement type
}
