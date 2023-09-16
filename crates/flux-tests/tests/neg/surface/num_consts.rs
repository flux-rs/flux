#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> (i8[i8::MAX], i8[i8::MIN]))]
fn test_i8() -> (i8, i8) {
    (i8::MIN, i8::MAX)
    //~^ ERROR refinement type error
    //~^^ ERROR refinement type error
}

#[flux::sig(fn() -> (i16[i16::MAX], i16[i16::MIN]))]
fn test_i16() -> (i16, i16) {
    (i16::MIN, i16::MAX)
    //~^ ERROR refinement type error
    //~^^ ERROR refinement type error
}

#[flux::sig(fn() -> (i32[i32::MAX], i32[i32::MIN]))]
fn test_i32() -> (i32, i32) {
    (i32::MIN, i32::MAX)
    //~^ ERROR refinement type error
    //~^^ ERROR refinement type error
}

#[flux::sig(fn() -> (i64[i64::MAX], i64[i64::MIN]))]
fn test_i64() -> (i64, i64) {
    (i64::MIN, i64::MAX)
    //~^ ERROR refinement type error
    //~^^ ERROR refinement type error
}

#[flux::sig(fn() -> (isize[isize::MAX], isize[isize::MIN]))]
fn test_isize() -> (isize, isize) {
    (isize::MIN, isize::MAX)
    //~^ ERROR refinement type error
    //~^^ ERROR refinement type error
}

#[flux::sig(fn() -> (u8[u8::MAX], u8[u8::MIN]))]
fn test_u8() -> (u8, u8) {
    (u8::MIN, u8::MAX)
    //~^ ERROR refinement type error
    //~^^ ERROR refinement type error
}

#[flux::sig(fn() -> (u16[u16::MAX], u16[u16::MIN]))]
fn test_u16() -> (u16, u16) {
    (u16::MIN, u16::MAX)
    //~^ ERROR refinement type error
    //~^^ ERROR refinement type error
}

#[flux::sig(fn() -> (u32[u32::MAX], u32[u32::MIN]))]
fn test_u32() -> (u32, u32) {
    (u32::MIN, u32::MAX)
    //~^ ERROR refinement type error
    //~^^ ERROR refinement type error
}

#[flux::sig(fn() -> (u64[u64::MAX], u64[u64::MIN]))]
fn test_u64() -> (u64, u64) {
    (u64::MIN, u64::MAX)
    //~^ ERROR refinement type error
    //~^^ ERROR refinement type error
}

#[flux::sig(fn() -> (usize[usize::MAX], usize[usize::MIN]))]
fn test_usize() -> (usize, usize) {
    (usize::MIN, usize::MAX)
    //~^ ERROR refinement type error
    //~^^ ERROR refinement type error
}
