#![feature(register_tool)]
#![register_tool(flux)]

pub fn read_u16() -> u16 {
    let bytes: [u8; 2] = [10, 20];
    u16::from_le_bytes(bytes)
}
