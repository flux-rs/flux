#![feature(register_tool)]
#![register_tool(flux)]

// Bitwise BinOps
//
// We don't natively track any conditions on the bit-wise arithmetic operations,
// so all that we know is the type of the resulting value (although we know that
// it will unconditionally succeed).

#[flux::sig(fn(a: u32, b: u32) -> u32{v: v == a - b})]
pub fn uint_sub(a: u32, b: u32) -> u32 {
    a - b //~ ERROR overflow
}

#[flux::sig(fn(i32{v: v != 0}, i32) -> i32{v: v != 0})]
pub fn bitwise_or(a: i32, b: i32) -> i32 {
    a | b //~ ERROR postcondition
}

#[flux::sig(fn(a:i32, i32[0]) -> i32[a])]
pub fn bitwise_shl(a: i32, b: i32) -> i32 {
    a << b //~ ERROR postcondition
}

#[flux::sig(fn(a:i32, i32[0]) -> i32[a])]
pub fn bitwise_sh4(a: i32, b: i32) -> i32 {
    a >> b //~ ERROR postcondition
}

// Logical BinOps

// Should be {v: v == a || v == b}
#[flux::sig(fn(a: bool, b: bool) -> bool[a])]
pub fn logical_or(a: bool, b: bool) -> bool {
    a | b //~ ERROR postcondition
}

// Should be v == true
#[flux::sig(fn(bool[false], bool[true]) -> bool[false])]
pub fn logical_or_ft(a: bool, b: bool) -> bool {
    a | b //~ ERROR postcondition
}

// Should be v == false
#[flux::sig(fn(bool[false], bool[false]) -> bool[true])]
pub fn logical_or_ff(a: bool, b: bool) -> bool {
    a | b //~ ERROR postcondition
}
