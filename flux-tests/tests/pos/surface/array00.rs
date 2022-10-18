#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> [i32{v : v >= 0}; _])]
pub fn array00() -> [i32; 2] {
    [0, 1]
}

pub fn read_u16() -> u16 {
    let bytes: [u8; 2] = [10, 20];
    const BASE_PRIMES: [u32; 11] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31];
    u16::from_le_bytes(bytes)
}
