#![feature(register_tool)]
#![register_tool(flux)]

pub fn int_to_float() -> f32 {
    1i32 as f32
}

pub fn uint_to_float() -> f64 {
    42u8 as f64
}
