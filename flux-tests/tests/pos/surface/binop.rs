#![feature(register_tool)]
#![register_tool(flux)]

// Bitwise BinOps
//
// We don't natively track any conditions on the bit-wise arithmetic operations,
// so all that we know is the type of the resulting value (although we know that
// it will unconditionally succeed).

#[flux::sig(fn(i32{v: v > 0}, i32{v: v > 0}) -> i32)]
pub fn bitwise_or(a: i32, b: i32) -> i32 {
    a | b
}

#[flux::sig(fn(i32{v: v > 0}, i32{v: v > 0}) -> i32)]
pub fn bitwise_shl_i32_i32(a: i32, b:i32) -> i32 {
    a << b
}

#[flux::sig(fn(i32{v: v > 0}, u32{v: v > 0}) -> i32)]
pub fn bitwise_shl_i32_u32(a: i32, b:u32) -> i32 {
    a << b
}

#[flux::sig(fn(u32{v: v > 0}, i32{v: v > 0}) -> u32)]
pub fn bitwise_shl_u32_i32(a: u32, b:i32) -> u32 {
    a << b
}

#[flux::sig(fn(u32{v: v > 0}, u32{v: v > 0}) -> u32)]
pub fn bitwise_shl_u32_u32(a: u32, b:u32) -> u32 {
    a << b
}

#[flux::sig(fn(i32{v: v > 0}, i32{v: v > 0}) -> i32)]
pub fn bitwise_shr_i32_i32(a: i32, b:i32) -> i32 {
    a >> b
}

#[flux::sig(fn(i32{v: v > 0}, u32{v: v > 0}) -> i32)]
pub fn bitwise_shr_i32_u32(a: i32, b:u32) -> i32 {
    a >> b
}

#[flux::sig(fn(u32{v: v > 0}, i32{v: v > 0}) -> u32)]
pub fn bitwise_shr_u32_i32(a: u32, b:i32) -> u32 {
    a >> b
}

#[flux::sig(fn(u32{v: v > 0}, u32{v: v > 0}) -> u32)]
pub fn bitwise_shr_u32_u32(a: u32, b:u32) -> u32 {
    a >> b
}

// Logical BinOps
#[flux::sig(fn(a: bool, b: bool) -> bool{v: v == a || v == b})]
pub fn logical_or(a: bool, b: bool) -> bool {
    a | b
}

#[flux::sig(fn(bool{v: v == false}, bool{v: v == true}) -> bool{v: v == true})]
pub fn logical_or_ft(a: bool, b: bool) -> bool {
    a | b
}

#[flux::sig(fn(bool{v: v == false}, bool{v: v == false}) -> bool{v: v == false})]
pub fn logical_or_ff(a: bool, b: bool) -> bool {
    a | b
}
