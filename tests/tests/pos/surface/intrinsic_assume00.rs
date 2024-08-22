pub enum Mickey {
    A = 10,
    B = 20,
    C,
}

#[flux::sig(fn (z:_) -> i32{v: v==10 || v == 20 || v == 21})]
pub fn test_i32(z: Mickey) -> i32 {
    let res = z as i32;
    res
}

#[flux::sig(fn (z:_) -> u8{v: v==10 || v == 20 || v == 21})]
pub fn test_u8(z: Mickey) -> u8 {
    let res = z as u8;
    res
}
