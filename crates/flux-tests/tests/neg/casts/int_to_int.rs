#[flux::sig(fn() -> i32[0])]
pub fn bool_int() -> i32 {
    true as i32 //~ ERROR refinement type
}

#[flux::sig(fn() -> u32[1])]
pub fn bool_uint() -> u32 {
    false as u32 //~ ERROR refinement type
}

#[flux::sig(fn() -> u32[43])]
pub fn uint_uint_lossless() -> u32 {
    42u8 as u32 //~ ERROR refinement type
}

#[flux::sig(fn() -> i32[43])]
pub fn int_int_lossless() -> i32 {
    42i8 as i32 //~ ERROR refinement type
}

#[flux::sig(fn() -> i32[43])]
pub fn uint_int_lossless() -> i32 {
    42u8 as i32 //~ ERROR refinement type
}

#[flux::sig(fn() -> usize[42])]
pub fn unsigned_to_usize() -> usize {
    42u128 as usize //~ ERROR refinement type
}
