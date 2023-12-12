#![flux::cfg(check_overflow = true)]

// Arithmetic BinOps
// These check for over/underflow
#[flux::sig(fn(a: u32, b: u32) -> u32{v: v == a - b})]
pub fn uint_sub(a: u32, b: u32) -> u32 {
    a - b //~ ERROR overflow
}

#[flux::sig(fn(a: u32, b: u32) -> u32{v: v == a + b})]
pub fn uint_add(a: u32, b: u32) -> u32 {
    a + b //~ ERROR overflow
}

#[flux::sig(fn(a: i32{a > 0}, b: i32{b > 0}) -> i32{v: v == a + b})]
pub fn uint_add_pos(a: i32, b: i32) -> i32 {
    a + b //~ ERROR overflow
}

#[flux::sig(fn(a: i32{a < 0}, b: i32{b < 0}) -> i32{v: v == a + b})]
pub fn uint_add_neg(a: i32, b: i32) -> i32 {
    a + b //~ ERROR overflow
}

#[flux::sig(fn(a: i32) -> i32{v: v == a + 1})]
pub fn int_add1(a: i32) -> i32 {
    a + 1 //~ ERROR overflow
}

#[flux::sig(fn(a: u32) -> u32{v: v == a + 1})]
pub fn uint_add1(a: u32) -> u32 {
    a + 1 //~ ERROR overflow
}
