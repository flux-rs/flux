#![feature(register_tool)]
#![register_tool(flux)]

pub fn float_to_int() -> i32 {
    0.0f32 as i32
}

pub fn float_to_uint() -> u32 {
    1.0f64 as u32
}
