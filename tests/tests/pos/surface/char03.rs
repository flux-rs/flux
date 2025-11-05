use flux_rs::attrs::*;

pub fn cast_to_u32(x: char) -> u32 {
    let x = x as u32;
    x
}

pub fn cast_to_u16(x: char) -> u16 {
    let x = x as u16;
    x
}

pub fn cast_to_u8(x: char) -> u8 {
    let x = x as u8;
    x
}

#[spec(fn (x:char{ cast(x) < 256 }) -> char[x])]
pub fn cast_to_u8_and_back(x: char) -> char {
    let x = x as u8;
    let x = x as char;
    x
}

#[spec(fn (x:char['a']) -> u8[97])]
pub fn const_to_u8(x: char) -> u8 {
    let x = x as u8;
    x
}
