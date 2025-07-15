use flux_rs::attrs::*;

#[spec(fn (x:u8{10 < x}) -> u32 ensures 10int <= cast(x))]
pub fn test_cast_poly(x: u8) -> u32 {
    x as u32
}
