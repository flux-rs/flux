#![feature(register_tool)]
#![register_tool(flux)]

pub fn read_u16() -> u16 {
    let _bytes: [u8; 2] = [10, 20];
    12
    // u16::from_le_bytes(bytes)
}
