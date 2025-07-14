use flux_rs::attrs::*;

#[spec(fn (x:u8) -> u32[to_int(x)])]
pub fn test_int_to_int(x: u8) -> u32 {
    x as u32
}

#[spec(fn (x:char) -> u32[to_int(x)])]
pub fn test_char_to_int(x: char) -> u32 {
    x as u32
}

#[spec(fn (x:bool) -> u32[to_int(x)])]
pub fn test_bool_to_int(x: bool) -> u32 {
    x as u32
}

#[spec(fn (x:bool) -> u32[to_int(x)])]
pub fn test_bool_to_int_with_if(x: bool) -> u32 {
    if x { 1 } else { 0 }
}

pub struct S {}

#[spec(fn(x:S, n:usize[to_int(x)]) -> usize[to_int(x)])]
pub fn foo(_x: S, n: usize) -> usize {
    n
}
