#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> [i32{v : v >= 0}; _])]
pub fn array00() -> [i32; 2] {
    [0, 1]
}

pub fn read_u16() -> u16 {
    let bytes: [u8; 2] = [10, 20];
    u16::from_le_bytes(bytes)
}
