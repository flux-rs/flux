#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> [i32{v : v >= 0}; 2])]
pub fn array00() -> [i32; 2] {
    [0, 1]
}

pub fn read_u16() -> u16 {
    let bytes: [u8; 2] = [10, 20];
    u16::from_le_bytes(bytes)
}

#[flux::sig(fn() -> i32{v : v > 10})]
pub fn write() -> i32 {
    let bytes: [i32; 2] = [10, 20];
    bytes[0] + bytes[1]
}
